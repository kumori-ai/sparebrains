"""The judge. A .lean file is VERIFIED only if the kernel accepts it, no `sorry`
survives, and every theorem in it depends on nothing outside the axiom allowlist.

    python3 tools/check.py --expect accept checks/accept/*.lean
    python3 tools/check.py --expect reject checks/reject/*.lean
    python3 tools/check.py --expect wellformed --jobs 2 targets/minif2f/test/*.lean

`wellformed` is the target-set gate: the statement type-checks and its only hole is
`sorryAx`. Exit 0 iff every file's verdict matches --expect. Runs `lake env lean` per
file (needs the lake workspace built and the mathlib cache present). The judge sets
`autoImplicit=false` itself, so an attempt cannot turn a typo into a free variable.
"""
import argparse, itertools, json, os, re, resource, secrets, signal, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEAN_FLAGS = ["-DautoImplicit=false", "-DrelaxedAutoImplicit=false"]
DECL_RE = re.compile(r"^\s*(?:theorem|lemma)\s+([^\s:({\[]+)", re.M)
AXIOMS_RE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS_RE = re.compile(r"'([^']+)' does not depend on any axioms")
# A candidate is untrusted code: `#eval` runs IO while Lean elaborates, and Lean's output is
# published. So Lean gets only what it needs to find lake and mathlib, never a key. In Actions,
# SB_JUDGE_USER (tools/judge_sandbox.sh) also runs it as another user, because a process of the
# same user can read its parent's secrets from /proc/<pid>/environ.
ENV_KEEP = {"PATH", "HOME", "LANG", "LC_ALL", "TMPDIR", "ELAN_HOME", "ELAN_TOOLCHAIN"}


JUDGE_SLICE = "sbjudge.slice"   # the cgroup every scoped Lean run sits in: one memory limit over all of them (#683)


# How a run the kernel's memory limit killed ends: its SIGKILL, or the SIGTERM systemd stops the scope with when it
# sees the kill first (2 of 11 kills the kernel log named, check run 43333405589), as the signal or as lake's exit.
KILLED = (-9, 137, -15, 143)
_units = itertools.count(1)


def new_unit():
    """A scope name no other check has: systemd refuses a name in use, and a killed scope keeps its name."""
    return f"sbjudge-{os.getpid()}-{next(_units)}-{secrets.token_hex(4)}"


def mem_limit():
    """The memory limit in MB on each Lean run, set by tools/judge_sandbox.sh with the slice's; None when there is none."""
    return int(os.environ.get("SB_JUDGE_MEM_MB") or 0) or None if os.environ.get("SB_JUDGE_USER") else None


def killed(rc):
    """What a run the memory limit killed is reported as, in place of its output; None for any other end."""
    return f"killed (exit {rc}) under the {mem_limit()} MB memory limit" if rc in KILLED and mem_limit() else None


def unfinished(text):
    """Lean did not finish, at our timeout or the kernel's memory limit: the text says nothing about the proof.
    Every reader of a judge reason or of lean_tools.run_lean's output asks this, never the words themselves."""
    return "timeout after" in text or "MB memory limit" in text


def lean_cmd(file, unit=None, mem_mb=None):
    """Lean on one file, as the judge user when there is one. With a memory limit (mem_limit(), or `mem_mb` from the
    canary) it runs in a systemd scope of its own inside JUDGE_SLICE, held to that limit with no swap, its oom group
    set so a check the kernel kills dies whole (lake and Lean), under the slice's limit over all checks together.
    Measured on the runner 2026-11-12 (tools/judge_memory_canary.py, check runs 43336349606 and 43338876083): at
    4000 MB a scope and 8000 MB the slice, runaways died in 5-12 s with 6.9 GB still free, no proof beside them was
    lost in 42 runs, warm cache and cold; with the slice's limit alone one of 12 was (43333405589). Lean's own -M is
    not a limit: it compares resident memory, the mapped Mathlib files included (about 6.6 GB there), on a counter
    and throws; a runaway in #eval printed the message and ran on (43326406123)."""
    env = {k: v for k, v in os.environ.items() if k in ENV_KEEP or k.startswith(("LAKE", "LEAN"))}
    cmd = ["lake", "env", "lean", *LEAN_FLAGS, file]
    user = os.environ.get("SB_JUDGE_USER")
    if not user:
        return cmd, env
    env["HOME"] = f"/tmp/{user}"
    mem_mb = mem_mb or mem_limit()
    return as_judge(cmd, env, user, unit or (new_unit() if mem_mb else None), mem_mb), env


def as_judge(cmd, env, user, unit=None, mem_mb=None):
    """`cmd` as the judge user with only `env`; in the scope `unit` of JUDGE_SLICE when one is named, held to
    `mem_mb` of its own memory and no swap when that is given."""
    how = ["-u", user] if not unit else ["systemd-run", "--scope", "--quiet", f"--unit={unit}", f"--slice={JUDGE_SLICE}",
                                         f"--uid={user}", "-p", "OOMPolicy=kill",
                                         *(["-p", f"MemoryMax={mem_mb}M", "-p", "MemorySwapMax=0"] if mem_mb else [])]
    return ["sudo", "-n", *how, "env", "-i", *(f"{k}={v}" for k, v in env.items()), *cmd]


def kill_tree(pid, user=None):
    """Stop `pid` and everything under it. `lake env lean` is Lean's parent, and in Actions sudo's too, so killing
    only the process we started leaves Lean running: run 43142012823 (2026-11-12) had five timed-out checks behind it
    when its runner was shut down, and locally an orphaned Lean held 2.96 GB 6 s after its timeout, 3.27 GB 20 s on.
    The tree is read before anything dies, while the parent links still hold. Lean runs as the judge user in
    Actions, whose processes this job's user can only signal through sudo. Known limits, as of 2026-11-12 (Codex
    20261112T201242695422Z f5, f6): a pid reused between the table read and the kill would be signaled, and a
    descendant that re-parented itself before the read is not in the tree (it was not stopped before either)."""
    try:                                                  # no table: the process we started still dies below
        table = subprocess.run(["ps", "-axo", "pid=,ppid="], capture_output=True, text=True, timeout=HELPER_S).stdout
    except (OSError, subprocess.TimeoutExpired):
        table = ""
    kids = {}
    for child, parent in (l.split() for l in table.splitlines()):
        kids.setdefault(int(parent), []).append(int(child))
    tree, todo = [], [pid]
    while todo:
        tree.append(todo.pop())
        todo += kids.get(tree[-1], [])
    if user:
        try:
            subprocess.run(["sudo", "-n", "kill", "-KILL", *map(str, tree)], capture_output=True, timeout=HELPER_S)
        except (OSError, subprocess.TimeoutExpired):
            pass
    for p in tree:                                        # ours, and all of them when there is no judge user
        try:
            os.kill(p, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
    return tree


HELPER_S = 30                # ps, sudo kill and the wait for a killed tree each get this long, never forever (Codex f3)
_last = threading.local()


def last_peak_mb():
    """Peak resident memory, in MB, of the last Lean run this thread finished; None when it was killed at its timeout
    (a killed tree was never waited for, so the kernel has no figure for it)."""
    return getattr(_last, "peak_mb", None)


def run_lean(cmd, env, timeout, cwd=None):
    """(returncode, stdout, stderr, peak MB) of one Lean run; returncode None when it hit `timeout`, and then its
    whole tree is stopped (kill_tree) and stdout/stderr are what it had written. The peak is the kernel's own figure
    for the process and the children it waited for (wait4), in a log line so a run that dies still shows it."""
    with tempfile.TemporaryFile() as fo, tempfile.TemporaryFile() as fe:
        p = subprocess.Popen(cmd, env=env, cwd=cwd, stdout=fo, stderr=fe, stdin=subprocess.DEVNULL)
        end, rc, peak = time.monotonic() + timeout, None, None
        while True:
            pid, status, usage = os.wait4(p.pid, os.WNOHANG)
            if pid:
                rc = os.waitstatus_to_exitcode(status)
                peak = round(usage.ru_maxrss / (1048576 if sys.platform == "darwin" else 1024))   # bytes on macOS, KB on Linux
                break
            if time.monotonic() >= end:
                kill_tree(p.pid, os.environ.get("SB_JUDGE_USER"))
                gone = time.monotonic() + HELPER_S
                while not os.wait4(p.pid, os.WNOHANG)[0] and time.monotonic() < gone:
                    time.sleep(0.05)
                break
            time.sleep(0.05)
        p.returncode = -9 if rc is None else rc          # reaped here: Popen must not wait for it again
        _last.peak_mb = peak
        fo.seek(0), fe.seek(0)
        # as subprocess's text mode read it: \r\n and \r are \n; a byte that is not UTF-8 no longer raises
        text = lambda b: b.decode(errors="replace").replace("\r\n", "\n").replace("\r", "\n")
        return rc, text(fo.read()), text(fe.read()), peak


def judge(path, timeout):
    src = Path(path).read_text()
    names = DECL_RE.findall(src)
    if not names:
        return "reject", "no theorem or lemma declared", 0.0, ""
    probe = src.rstrip("\n") + "\n\n" + "\n".join(f"#print axioms {n}" for n in names) + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tmp:
        tmp.write(probe)
    os.chmod(tmp.name, 0o644)                    # the judge user must read it
    cmd, env = lean_cmd(tmp.name)
    t0 = time.monotonic()
    try:
        rc, stdout, stderr, _ = run_lean(cmd, env, timeout)
    finally:
        os.unlink(tmp.name)
    secs = time.monotonic() - t0
    if rc is None:
        return "reject", f"timeout after {timeout}s", secs, ""
    if killed(rc):                                       # like a timeout: it says nothing about the proof itself
        return "reject", killed(rc), secs, ""
    out = (stdout + stderr).replace(tmp.name, path)
    if rc != 0:
        first_error = next((l for l in out.splitlines() if "error" in l), out[:200])
        return "reject", f"lean exit {rc}: {first_error.strip()}", secs, out
    audited = {n for n, _ in AXIOMS_RE.findall(out)} | set(NO_AXIOMS_RE.findall(out))
    missing = set(names) - audited
    if missing:
        return "reject", f"no axiom report for {sorted(missing)}", secs, out
    holes = False
    for name, axioms in AXIOMS_RE.findall(out):
        used = {a.strip() for a in axioms.split(",") if a.strip()}
        bad = used - ALLOWED_AXIOMS - {"sorryAx"}
        if bad:
            return "reject", f"{name} depends on disallowed axioms {sorted(bad)}", secs, out
        holes |= "sorryAx" in used   # the kernel's word, not the elaborator's warning
    if holes:
        return "wellformed", f"statement type-checks, proof is sorry {names}", secs, out
    return "accept", f"kernel accepted {names}", secs, out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--expect", choices=["accept", "reject", "wellformed"], required=True)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    rows, ok = [], True
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda f: (f, *judge(f, args.timeout)), args.files))
    for f, verdict, reason, secs, out in results:
        # `reject` is satisfied by anything short of a full acceptance
        matched = verdict != "accept" if args.expect == "reject" else verdict == args.expect
        ok &= matched
        rows.append((f, verdict, matched, secs, reason))
        print(json.dumps({"file": f, "verdict": verdict, "expected": args.expect,
                          "ok": matched, "seconds": round(secs, 1), "reason": reason}))
        if args.verbose or not matched:
            print(out, file=sys.stderr)

    peak_mb = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss // 1024
    print(f"peak child RSS {peak_mb} MB")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as fh:
            fh.write(f"### expect `{args.expect}`  (peak child RSS {peak_mb} MB)\n\n")
            fh.write("| file | verdict | ok | s | reason |\n|---|---|---|---|---|\n")
            for f, v, m, s, r in rows:
                fh.write(f"| `{f}` | {v} | {'✅' if m else '❌'} | {s:.1f} | {r} |\n")
            fh.write("\n")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
