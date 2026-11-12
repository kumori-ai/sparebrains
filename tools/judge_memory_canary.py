"""Measures in Actions what a Lean memory cap (-M) does, to pick one (kumori #683). Needs tools/judge_sandbox.sh first.

Run 43142012823 (2026-11-12) was shut down by its runner with 177 calls unpublished; whether a check ran away with the
memory is not known. The cap counts the Mathlib import, and how much that is differs by machine: the first runner
reading (run 43301409108, 2026-11-12) had -M 4000 and 4500 stop all 45 sampled proofs and every capped run exit 134
at a 6,072 MB peak after about 70 s, where an uncapped accept there takes 4.5 s and peaks 6,630 MB, and macOS passes
at 3,400. So the caps are not fixed numbers: this first finds the floor, the lowest cap a plain accept passes here,
then tries the floor plus each HEADROOM. As the judge user and JOBS at once like the ladder, per cap:
  runaway: JOBS copies of a probe that allocates without end. Each must stop at the cap; the runner's lowest free
           memory while they ran is the number that says whether JOBS runaways at once fit.
  verified: a spread of proofs the kernel already accepted. Each must still accept; one stopped by the cap means the
            cap would turn real proofs into rejects.
The probe must be seen taking memory (else a calm reading means nothing): its peak must be MIN_TAKEN_MB over the
plain accept's. Free memory cannot say so, the import alone moved it 1.6 GB in that run. Prints one line per arm
with its seconds; exits 1 when no cap is a floor, a runaway is not stopped or not seen, or no cap keeps every proof.
A cap is named only when the whole sample passed under it JOBS at once; a timeout or any other failure names none
(Codex 20261112T230227845584Z f1). Not bounded, as of 2026-11-12 (same verdict, f2): nothing limits what JOBS
runaways take together, so an arm that exhausts the runner ends the run with the lines printed so far."""
import os, shutil, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import check

ROOT = Path(__file__).parent.parent
PROBE = ROOT / "checks/canary/memory_probe.lean"
PLAIN = ROOT / "checks/accept/two_plus_two.lean"
FLOOR_CAPS, HEADROOM, JOBS, SAMPLE = range(5000, 9001, 500), (500, 1000, 2000), 3, 45
RUNAWAY_S, PROOF_S, MIN_TAKEN_MB = 180, 600, 300


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


def floor(caps, plain):
    """(the lowest of `caps` under which plain(cap) passes, its peak MB), or (None, None). plain(cap) is lean()'s result."""
    for cap in caps:
        t0 = time.monotonic()
        rc, out, peak = plain(cap)
        print(f"floor, cap {cap}: plain accept exit {rc}, peak {peak} MB, {time.monotonic() - t0:.0f} s", flush=True)
        if rc == 0:
            return cap, peak
        if rc is None or not check.capped(out):          # a timeout reads nothing, whatever it printed
            sys.exit(f"floor, cap {cap}: the plain accept failed and not at the cap, so this reads nothing: {out[-300:]}")
    return None, None


def blind(peaks, plain_peak):
    """A runaway was not seen taking memory: some peak is not MIN_TAKEN_MB over a plain accept's, or was not read."""
    return plain_peak is None or any(p is None or p - plain_peak < MIN_TAKEN_MB for p in peaks)


def runaway(cap, plain_peak):
    """The reasons this cap's reading fails, empty when every runaway was stopped by the cap and seen taking memory."""
    t0 = time.monotonic()
    with ThreadPoolExecutor(JOBS) as pool:
        res, low, before = watched(lambda: list(pool.map(lambda _: lean(PROBE, cap, RUNAWAY_S), range(JOBS))))
    stopped, peaks = [check.capped(out) for rc, out, peak in res], [peak for _, _, peak in res]
    print(f"cap {cap}: {JOBS} runaways at once, {sum(stopped)} stopped by the cap, exits {[rc for rc, _, _ in res]}, "
          f"peaks {peaks} MB (plain accept {plain_peak}); free memory {before} -> lowest {low} MB; "
          f"{time.monotonic() - t0:.0f} s", flush=True)
    bad = []
    if not all(stopped):
        bad.append(f"cap {cap}: a runaway was not stopped by its cap: {[out[-200:] for _, out, _ in res]}")
    if blind(peaks, plain_peak):
        bad.append(f"cap {cap}: peaks {peaks} MB against a plain accept's {plain_peak}: the probe was not seen taking memory")
    return bad


def verified(cap, files):
    """(the files the cap stopped, [(file, exit)] that failed some other way: a timeout's exit is None)."""
    t0 = time.monotonic()
    def one(f):
        rc, out, peak = lean(f, cap, PROOF_S)
        return f, rc, rc is not None and check.capped(out), peak   # a timeout is never "stopped by the cap"
    with ThreadPoolExecutor(JOBS) as pool:
        res, low, before = watched(lambda: list(pool.map(one, files)))
    cut = [f for f, rc, capped, _ in res if capped]
    other = [(f, rc) for f, rc, capped, _ in res if rc != 0 and not capped]
    peaks = sorted(p for _, _, _, p in res if p)
    print(f"cap {cap}: {len(files)} verified proofs, {sum(rc == 0 for _, rc, _, _ in res)} pass, {len(cut)} stopped by "
          f"the cap, {len(other)} failed otherwise {other[:3]}; peak median {peaks[len(peaks) // 2] if peaks else None} "
          f"max {peaks[-1] if peaks else None} MB; free memory {before} -> lowest {low} MB; "
          f"{time.monotonic() - t0:.0f} s", flush=True)
    return cut, other


def main(files):
    try:
        cores = Path("/proc/sys/kernel/core_pattern").read_text().strip()   # where a capped run's abort goes
    except OSError:
        cores = None
    print(f"judge user: {os.environ.get('SB_JUDGE_USER') or 'none'}; {free_mb()} MB free; {len(files)} proofs sampled; "
          f"core_pattern {cores!r}", flush=True)
    low, plain_peak = floor(FLOOR_CAPS, lambda cap: lean(PLAIN, cap, PROOF_S))
    if low is None:
        sys.exit(f"no cap up to {FLOOR_CAPS[-1]} passes a plain accept: no floor, nothing else read")
    caps = [low + h for h in HEADROOM]
    print(f"floor {low} MB; caps tried: {caps}", flush=True)
    bad = [b for cap in caps for b in runaway(cap, plain_peak)]   # every cap's reading, whichever cap the proofs need
    left, keeps = files, None
    for cap in caps:
        cut, other = verified(cap, left)                 # a proof cut at this cap is tried again at the next
        if not cut and not other and left is not files:  # the retries ran few at a time: the whole sample, JOBS at once
            cut, other = verified(cap, files)
            left = files
        if other:                                        # a timeout or an error is not a proof the cap kept
            bad.append(f"cap {cap}: {len(other)} sampled proofs failed and not at the cap, so no cap is named: {other[:5]}")
            break
        if not cut:
            keeps = cap
            break
        left = cut
    else:
        bad.append(f"no cap up to {caps[-1]} keeps every sampled proof: {left}")
    if bad:
        sys.exit("\n".join(bad))
    print(f"lowest cap that keeps every sampled proof: {keeps} (floor {low} + {keeps - low})")


if __name__ == "__main__":
    files = spread(subprocess.run(["git", "ls-files", "verified"], capture_output=True, text=True, cwd=ROOT,
                                  check=True).stdout.split(), SAMPLE)
    files = [str(ROOT / f) for f in files if f.endswith(".lean")]
    if len(files) < 10:
        sys.exit(f"only {len(files)} verified proofs to sample: verdict meaningless")
    main(files)
