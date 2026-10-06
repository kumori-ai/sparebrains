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
import argparse, json, os, re, resource, subprocess, sys, tempfile, time
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


def lean_cmd(file):
    env = {k: v for k, v in os.environ.items() if k in ENV_KEEP or k.startswith(("LAKE", "LEAN"))}
    cmd = ["lake", "env", "lean", *LEAN_FLAGS, file]
    user = os.environ.get("SB_JUDGE_USER")
    if not user:
        return cmd, env
    env["HOME"] = f"/tmp/{user}"
    return ["sudo", "-n", "-u", user, "env", "-i", *(f"{k}={v}" for k, v in env.items()), *cmd], env


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
        run = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        os.unlink(tmp.name)
        return "reject", f"timeout after {timeout}s", time.monotonic() - t0, ""
    os.unlink(tmp.name)
    secs = time.monotonic() - t0
    out = (run.stdout + run.stderr).replace(tmp.name, path)
    if run.returncode != 0:
        first_error = next((l for l in out.splitlines() if "error" in l), out[:200])
        return "reject", f"lean exit {run.returncode}: {first_error.strip()}", secs, out
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
