"""Measures in Actions what a Lean memory cap (-M) does, to pick one (kumori #683). Needs tools/judge_sandbox.sh first.

Run 43142012823 (2026-11-12) was shut down by its runner with 177 calls unpublished; whether a check ran away with the
memory is not known. For each candidate cap this runs, as the judge user and JOBS at once like the ladder:
  runaway: JOBS copies of a probe that allocates without end. Each must stop at the cap; the runner's lowest free
           memory while they ran is the number that says whether JOBS runaways at once fit.
  verified: a spread of proofs the kernel already accepted. Each must still accept; one stopped by the cap means the
            cap would turn real proofs into rejects.
The probe must be seen taking memory (else a calm reading means nothing). Prints one line per arm; exits 1 when a
runaway is not stopped by its cap, or when no cap keeps every sampled proof."""
import os, shutil, subprocess, sys, tempfile, threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import check

ROOT = Path(__file__).parent.parent
PROBE = ROOT / "checks/canary/memory_probe.lean"
CAPS, JOBS, SAMPLE = (4000, 4500, 6000), 3, 45
RUNAWAY_S, PROOF_S, MIN_TAKEN_MB = 180, 600, 500


def free_mb(meminfo="/proc/meminfo"):
    """The kernel's MemAvailable in MB; None off Linux."""
    try:
        kb = {l.split(":")[0]: int(l.split()[1]) for l in Path(meminfo).read_text().splitlines() if ":" in l}
        return kb["MemAvailable"] // 1024
    except (OSError, KeyError, ValueError, IndexError):
        return None


def spread(files, n):
    """n of the sorted files, evenly spaced, at most one per problem directory: the same sample every run."""
    first = {}
    for f in sorted(files):
        first.setdefault(str(Path(f).parent), f)
    one = sorted(first.values())
    if len(one) <= n:
        return one
    return [one[i * len(one) // n] for i in range(n)]


def lean(path, cap, timeout):
    """(returncode or None, output, peak MB) of Lean on a copy of `path` under `cap`, as the judge runs it."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tmp:
        shutil.copyfileobj(open(path), tmp)
    os.chmod(tmp.name, 0o644)
    try:
        cmd, env = check.lean_cmd(tmp.name, cap)
        rc, out, err, peak = check.run_lean(cmd, env, timeout, cwd=ROOT)
        return rc, out + err, peak
    finally:
        os.unlink(tmp.name)


def watched(work):
    """(work's result, lowest free MB seen while it ran, free MB before it)."""
    before, low, done = free_mb(), [free_mb()], threading.Event()
    def sample():
        while not done.wait(0.2):
            low.append(free_mb())
    t = threading.Thread(target=sample)
    t.start()
    try:
        return work(), min((x for x in low if x is not None), default=None), before
    finally:
        done.set()
        t.join()


def runaway(cap):
    with ThreadPoolExecutor(JOBS) as pool:
        res, low, before = watched(lambda: list(pool.map(lambda _: lean(PROBE, cap, RUNAWAY_S), range(JOBS))))
    stopped = [check.capped(out) for rc, out, peak in res]
    print(f"cap {cap}: {JOBS} runaways at once, {sum(stopped)} stopped by the cap, exits {[rc for rc, _, _ in res]}, "
          f"peaks {[peak for _, _, peak in res]} MB; free memory {before} -> lowest {low} MB", flush=True)
    if not all(stopped):
        sys.exit(f"cap {cap}: a runaway was not stopped by its cap: {[out[-200:] for _, out, _ in res]}")
    if low is not None and before - low < MIN_TAKEN_MB:
        sys.exit(f"cap {cap}: free memory moved {before - low} MB, so the probe was not seen taking memory: blind")
    return low


def verified(cap, files):
    def one(f):
        rc, out, peak = lean(f, cap, PROOF_S)
        return f, rc, check.capped(out), peak
    with ThreadPoolExecutor(JOBS) as pool:
        res, low, before = watched(lambda: list(pool.map(one, files)))
    cut = [f for f, rc, capped, _ in res if capped]
    other = [(f, rc) for f, rc, capped, _ in res if rc != 0 and not capped]
    peaks = sorted(p for _, _, _, p in res if p)
    print(f"cap {cap}: {len(files)} verified proofs, {sum(rc == 0 for _, rc, _, _ in res)} pass, {len(cut)} stopped by "
          f"the cap, {len(other)} failed otherwise {other[:3]}; peak median {peaks[len(peaks) // 2] if peaks else None} "
          f"max {peaks[-1] if peaks else None} MB; free memory {before} -> lowest {low} MB", flush=True)
    return cut


if __name__ == "__main__":
    files = spread(subprocess.run(["git", "ls-files", "verified"], capture_output=True, text=True, cwd=ROOT,
                                  check=True).stdout.split(), SAMPLE)
    files = [str(ROOT / f) for f in files if f.endswith(".lean")]
    if len(files) < 10:
        sys.exit(f"only {len(files)} verified proofs to sample: verdict meaningless")
    print(f"judge user: {os.environ.get('SB_JUDGE_USER') or 'none'}; {free_mb()} MB free; {len(files)} proofs sampled", flush=True)
    for cap in CAPS:                                     # every cap's runaway reading, whichever cap the proofs need
        runaway(cap)
    left = files
    for cap in CAPS:
        left = verified(cap, left)                       # a proof cut at this cap is tried again at the next
        if not left:
            print(f"lowest cap that keeps every sampled proof: {cap}")
            break
    else:
        sys.exit(f"no cap up to {CAPS[-1]} keeps every sampled proof: {left}")
