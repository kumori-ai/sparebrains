"""Measures in Actions what a judge timeout leaves behind. Needs tools/judge_sandbox.sh first.

Run 43142012823 (2026-11-12) was shut down by its runner after five checks hit the 300 s timeout; locally a timed-out
check left Lean running with 2.96 GB. This runs one probe that never finishes, twice, as the judge user:
  old: subprocess.run(timeout=), as check.judge did until 2026-11-12, then counts the Lean processes still alive
  new: check.run_lean, which stops the whole tree, and must leave none
The probe is seen running before either timeout (else the count is blind and stops here). Prints what each way left,
with its memory, so the log carries the measurement; exits 1 only when the new way leaves a process."""
import os, shutil, subprocess, sys, tempfile, time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import check

PROBE = Path(__file__).parent.parent / "checks/canary/timeout_probe.lean"
USER = os.environ.get("SB_JUDGE_USER")
TIMEOUT_S, SETTLE_S, HELPER_S = 45, 8, 30


def leans(name):
    """{pid: resident MB} of the Lean processes checking the probe's copy: the program is `lean` itself, never the
    sudo, env or lake around it (a launcher stalled before Lean would pass for it; Codex 20261112T200455784944Z f1).
    A process table that cannot be read stops the canary: an empty one would read as nothing left alive (f2)."""
    r = subprocess.run(["ps", "-axo", "pid=,rss=,command="], capture_output=True, text=True, timeout=HELPER_S)
    if r.returncode != 0 or not r.stdout.strip():
        sys.exit(f"ps failed (exit {r.returncode}), so nothing can be counted: {r.stderr[-300:]}")
    rows = (l.split(None, 2) for l in r.stdout.splitlines() if name in l)
    return {int(pid): round(int(rss) / 1024) for pid, rss, cmd in rows if Path(cmd.split()[0]).name == "lean"}


def free_gb():
    try:
        kb = {l.split(":")[0]: int(l.split()[1]) for l in Path("/proc/meminfo").read_text().splitlines() if ":" in l}
        return f"{kb['MemAvailable'] / 1048576:.1f} GB free"
    except (OSError, KeyError):
        return "free memory unread (no /proc/meminfo)"


def arm(label, run):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tmp:
        shutil.copyfileobj(PROBE.open(), tmp)
    os.chmod(tmp.name, 0o644)
    cmd, env = check.lean_cmd(tmp.name)
    left = {}
    try:
        seen = {}
        watch = lambda: seen.update(leans(tmp.name))
        run(cmd, env, watch)
        if not seen:
            sys.exit(f"{label}: the probe was never seen running, so a count of zero would mean nothing")
        time.sleep(SETTLE_S)
        left = leans(tmp.name)
        print(f"{label}: {len(seen)} Lean process(es) seen while it ran; {SETTLE_S} s after the {TIMEOUT_S} s timeout "
              f"{len(left)} still alive {sorted(left.values())} MB; {free_gb()}", flush=True)
        return left
    finally:
        try:                                             # whatever stopped the arm, its probe does not outlive it (Codex f4)
            left = leans(tmp.name)
        except (SystemExit, OSError, subprocess.SubprocessError):
            pass
        if left:
            subprocess.run((["sudo", "-n"] if USER else []) + ["kill", "-KILL", *map(str, left)], capture_output=True,
                           timeout=HELPER_S)
        os.unlink(tmp.name)


def old(cmd, env, watch):
    p = subprocess.Popen(cmd, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        time.sleep(TIMEOUT_S - 5)
        watch()
        time.sleep(5)
    finally:
        p.kill()                                         # what subprocess.run(timeout=) does: the one process it started
        p.wait(timeout=HELPER_S)


def new(cmd, env, watch):
    import threading
    t = threading.Timer(TIMEOUT_S - 5, watch)
    t.start()
    rc = check.run_lean(cmd, env, TIMEOUT_S)[0]
    t.join()
    if rc is not None:
        sys.exit(f"new: the probe ended by itself (exit {rc}) before the timeout: it measures nothing")


if __name__ == "__main__":
    print(f"judge user: {USER or 'none (Lean runs as this user)'}; {free_gb()}", flush=True)
    was = arm("old", old)
    now = arm("new", new)
    if now:
        sys.exit(f"a timed-out check still leaves Lean running: {now}")
    print(f"timeout leaves nothing behind (the old way left {len(was)})")
