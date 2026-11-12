"""Measures in Actions whether one kernel memory limit over every judge Lean run holds (kumori #683). Needs
tools/judge_sandbox.sh first. Measure only: the judge sets no limit.

Run 43142012823 (2026-11-12) was shut down by its runner with 177 calls unpublished. Lean's own -M is not the answer,
as of 2026-11-12 (check run 43326406123, Lean v4.33.1 src/runtime/memory.cpp check_memory): it compares resident
memory, mapped Mathlib files included, on a counter and throws. A plain accept needs -M 7000 on the runner (peak
6,621 MB; macOS 3,400); three runaways under -M 7500 and 8000 printed the message and were still running at the
180 s timeout; under 9000 the step got SIGTERM in 32 s and the job ended.

So this measures the kernel's limit instead (cgroup v2 memory.max): every Lean run in its own scope of one slice
(check.lean_cmd unit=), the limit on the slice, swap 0. One limit over all and not one per check, because the checks
share the Mathlib mapping and the kernel charges a shared area to one cgroup, which one is not determined. For each
of LIMITS, as the judge user:
  guard:    a scope really is in the slice, as the judge user, with its oom group set, and a plain accept passes.
  runaway:  JOBS copies of a probe that allocates without end. Each must be killed, and the kernel log must name
            its scope as killed by the cgroup's limit; a kill the host's own out-of-memory made counts against.
  mixed:    runaways one after another beside verified proofs running back to back. Every proof must pass, and at
            least MIN_MET of them must have been running at the moment of a kill, else this says nothing about
            what a kill does to the checks beside it.
  verified: the sample of verified proofs, JOBS at once. Every one must pass.
A limit is listed only when every arm held under it; a timeout or any failure lists none, and the run exits 1 with
the reasons. Between arms it waits for the slice to be empty (cgroup.events populated, which counts the scopes
under it). Codex 20261112T233227563378Z f1-f3 (the emptiness, attribution and overlap rules)."""
import itertools, os, shutil, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import check

ROOT = Path(__file__).parent.parent
PROBE = ROOT / "checks/canary/memory_probe.lean"
PLAIN = ROOT / "checks/accept/two_plus_two.lean"
CG = Path("/sys/fs/cgroup") / check.JUDGE_SLICE
LIMITS, JOBS, SAMPLE = (8000, 9000, 10000), 3, 45
RUNAWAY_S, PROOF_S, SETTLE_S = 180, 600, 60
MIXED_RUNAWAYS, MIN_MET = 5, 5
KILLED = (-9, 137)                                       # SIGKILL, as the signal or as lake's exit status
_units = itertools.count(1)


def unit():
    return f"sbjudge-{os.getpid()}-{next(_units)}"


def sudo(*cmd):
    return subprocess.run(["sudo", "-n", *cmd], capture_output=True, text=True, timeout=check.HELPER_S)


def read(path):
    try:
        return Path(path).read_text().strip()
    except OSError:
        return None


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


def limit_killed(log, unit):
    """The kernel log says the cgroup's limit killed this check's scope (mm/oom_kill.c, memory.oom.group)."""
    return any(f"/{unit}.scope " in l and "memory.oom.group" in l for l in log.splitlines())


def host_kills(log):
    """Out-of-memory kills in the kernel log that no cgroup's limit made: the whole machine ran out."""
    return sum("Killed process" in l and "Memory cgroup out of memory" not in l for l in log.splitlines())


def overlapping(runs, kills):
    """The (file, exit, start, end) runs that were going at the moment of some kill."""
    return [r for r in runs if any(r[2] < k < r[3] for k in kills)]


def lean(path, unit, timeout):
    """(returncode or None, output, peak MB, start, end) of Lean on a copy of `path` in the scope `unit`."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tmp:
        shutil.copyfileobj(open(path), tmp)
    os.chmod(tmp.name, 0o644)
    try:
        cmd, env = check.lean_cmd(tmp.name, unit)
        t0 = time.monotonic()
        rc, out, err, peak = check.run_lean(cmd, env, timeout, cwd=ROOT)
        return rc, out + err, peak, t0, time.monotonic()
    finally:
        os.unlink(tmp.name)


def set_limit(mb):
    sudo("systemctl", "start", check.JUDGE_SLICE)
    r = sudo("systemctl", "set-property", "--runtime", check.JUDGE_SLICE, f"MemoryMax={mb}M", "MemorySwapMax=0")
    if r.returncode != 0:                                # what the kernel then holds is read back in guard()
        sys.exit(f"limit {mb}: systemd did not take the limit: blind. {r.stderr.strip()[-300:]}")


def guard(mb):
    """The plain accept's peak MB, after showing a scope is where and what the limit needs it to be."""
    user, u = os.environ.get("SB_JUDGE_USER"), unit()
    if not user:
        sys.exit("no judge user: nothing here runs in the slice, verdict meaningless")
    where = ('p=$(cut -d: -f3 /proc/self/cgroup); echo "$p"; cat "/sys/fs/cgroup$p/memory.oom.group"; id -un; '
             f'cat {CG}/memory.max {CG}/memory.swap.max')   # read from inside, while the slice surely exists
    r = subprocess.run(check.as_judge(["sh", "-c", where], {"PATH": os.environ["PATH"]}, user, u),
                       capture_output=True, text=True, timeout=check.HELPER_S)
    if r.stdout.split() != [f"/{check.JUDGE_SLICE}/{u}.scope", "1", user, str(mb * 1048576), "0"]:
        sys.exit(f"limit {mb}: a scope reports {r.stdout.split()} (its cgroup, oom group, user, the slice's limit and "
                 f"swap): blind. {r.stderr.strip()[-300:]}")
    rc, out, peak, t0, t1 = lean(PLAIN, unit(), PROOF_S)
    if rc != 0:
        sys.exit(f"limit {mb}: a plain accept in the slice exits {rc}: blind. {out[-300:]}")
    print(f"limit {mb}: guard, a scope is in the slice as {user} with its oom group set, limit and no swap read back; plain accept peak {peak} MB, "
          f"{t1 - t0:.0f} s; slice {charged()}", flush=True)
    return peak


def settle():
    """Returns once nothing is left in the slice or the scopes under it; stops the run when that cannot be had."""
    for kill in (False, True):
        if kill:
            sudo("systemctl", "kill", "--signal=KILL", check.JUDGE_SLICE)
        end = time.monotonic() + SETTLE_S
        while time.monotonic() < end:
            events = read(CG / "cgroup.events")
            if events is None and not CG.exists():       # systemd removed the empty slice's cgroup: nothing is in it
                return
            if events is None:
                sys.exit("the slice's cgroup.events cannot be read: blind")
            if "populated 0" in events:
                return
            time.sleep(0.2)
    sys.exit(f"the slice still holds processes {SETTLE_S} s after a kill: the next arm would not start clean")


def kernel_log():
    r = sudo("dmesg")
    if r.returncode != 0:
        sys.exit(f"the kernel log cannot be read, so no kill can be told from another: blind. {r.stderr.strip()[-200:]}")
    return r.stdout


def charged():
    """What the slice is charged with now, and its limit and kill counts."""
    stat = dict(l.split() for l in (read(CG / "memory.stat") or "").splitlines() if len(l.split()) == 2)
    mb = lambda v: int(v) // 1048576 if v and v.isdigit() else None
    events = " ".join((read(CG / "memory.events") or "").split())
    return (f"current {mb(read(CG / 'memory.current'))} MB (anon {mb(stat.get('anon'))}, file {mb(stat.get('file'))}, "
            f"mapped {mb(stat.get('file_mapped'))}); events: {events}")


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


def runaways(mb):
    """The reasons this limit did not contain JOBS runaways at once; empty when the limit killed each one."""
    units, host = [unit() for _ in range(JOBS)], host_kills(kernel_log())
    with ThreadPoolExecutor(JOBS) as pool:
        res, low, before = watched(lambda: list(pool.map(lambda u: lean(PROBE, u, RUNAWAY_S), units)))
    settle()
    log = kernel_log()
    by_limit = [limit_killed(log, u) for u in units]
    print(f"limit {mb}: {JOBS} runaways at once, exits {[r[0] for r in res]}, {sum(by_limit)} named by the kernel as "
          f"killed by the limit, after {[round(r[4] - r[3]) for r in res]} s, peaks {[r[2] for r in res]} MB; "
          f"free memory {before} -> lowest {low} MB; slice {charged()}", flush=True)
    bad = [f"limit {mb}: runaway {u} exit {r[0]}, named by the kernel: {named}. Not shown killed by the limit"
           for u, r, named in zip(units, res, by_limit) if r[0] not in KILLED or not named]
    if host_kills(log) > host:
        bad.append(f"limit {mb}: the machine itself ran out of memory while the runaways ran (kernel log)")
    return bad


def mixed(mb, files):
    """The reasons this limit's kills are not shown to leave the checks beside them alone."""
    runs, probes, stop, lock, queue = [], [], threading.Event(), threading.Lock(), itertools.cycle(files)
    host = host_kills(kernel_log())
    def proofs():
        while True:                                      # each worker finishes the proof it is on, and at least one
            with lock:
                f = next(queue)
            t0 = time.monotonic()
            try:
                rc, _, _, t0, t1 = lean(f, unit(), PROOF_S)
            except Exception as e:                       # a run with no reading is a failed run, never a missing one
                rc, t1 = f"{type(e).__name__}: {e}", time.monotonic()
            runs.append((f, rc, t0, t1))
            if stop.is_set():
                return
    workers = [threading.Thread(target=proofs) for _ in range(max(1, JOBS - 1))]
    def work():
        for w in workers:
            w.start()
        for _ in range(MIXED_RUNAWAYS):
            u = unit()
            rc, _, _, _, t1 = lean(PROBE, u, RUNAWAY_S)
            probes.append((u, rc, t1))
        stop.set()
        for w in workers:
            w.join()
    _, low, before = watched(work)
    settle()
    log = kernel_log()
    kills = [t1 for u, rc, t1 in probes if rc in KILLED and limit_killed(log, u)]
    met, failed = overlapping(runs, kills), [(Path(f).parent.name, rc) for f, rc, _, _ in runs if rc != 0]
    secs = lambda rs: round(sorted(r[3] - r[2] for r in rs)[len(rs) // 2]) if rs else None
    print(f"limit {mb}: mixed, {len(kills)} of {MIXED_RUNAWAYS} runaways killed by the limit beside {len(runs)} proof "
          f"runs, {len(runs) - len(failed)} pass, {len(failed)} failed {failed[:3]}; {len(met)} met the limit (running "
          f"at a kill), median {secs(met)} s against {secs([r for r in runs if r not in met])} s for the rest; "
          f"free memory {before} -> lowest {low} MB", flush=True)
    bad = []
    if len(kills) < MIXED_RUNAWAYS:
        bad.append(f"limit {mb}: mixed, {MIXED_RUNAWAYS - len(kills)} runaways not shown killed by the limit: {probes}")
    if failed:
        bad.append(f"limit {mb}: mixed, {len(failed)} proofs failed beside a runaway: {failed[:5]}")
    if len(met) < MIN_MET:
        bad.append(f"limit {mb}: mixed, {len(met)} proofs met the limit and {MIN_MET} are needed: no reading of what a kill does")
    if host_kills(log) > host:
        bad.append(f"limit {mb}: mixed, the machine itself ran out of memory (kernel log)")
    return bad


def verified(mb, files):
    """The reasons this limit does not keep the sample: any proof that did not pass, a timeout included."""
    with ThreadPoolExecutor(JOBS) as pool:
        res, low, before = watched(lambda: list(pool.map(lambda f: (f, *lean(f, unit(), PROOF_S)), files)))
    failed = [(Path(f).parent.name, rc) for f, rc, *_ in res if rc != 0]
    peaks, secs = sorted(r[3] for r in res if r[3]), sorted(r[5] - r[4] for r in res)
    print(f"limit {mb}: {len(files)} verified proofs {JOBS} at once, {len(files) - len(failed)} pass, {len(failed)} "
          f"failed {failed[:3]}; peak median {peaks[len(peaks) // 2] if peaks else None} max "
          f"{peaks[-1] if peaks else None} MB; median {secs[len(secs) // 2]:.0f} s, longest {secs[-1]:.0f} s; "
          f"free memory {before} -> lowest {low} MB; slice {charged()}", flush=True)
    return [f"limit {mb}: {len(failed)} sampled proofs did not pass: {failed[:5]}"] if failed else []


def main(files):
    print(f"judge user: {os.environ.get('SB_JUDGE_USER') or 'none'}; {free_mb()} MB free; {len(files)} proofs sampled; "
          f"limits tried: {list(LIMITS)}", flush=True)
    held, bad = [], []
    for mb in LIMITS:
        set_limit(mb)
        settle()
        guard(mb)
        loose = runaways(mb)
        if loose:                                        # a higher limit is not tried on runaways this one lost
            bad += loose
            break
        here = mixed(mb, files) + verified(mb, files)
        bad += here
        if not here:
            held.append(mb)
    if held:
        print(f"limits that held every arm: {held}", flush=True)
    if bad:
        sys.exit("\n".join(bad))


if __name__ == "__main__":
    files = spread(subprocess.run(["git", "ls-files", "verified"], capture_output=True, text=True, cwd=ROOT,
                                  check=True).stdout.split(), SAMPLE)
    files = [str(ROOT / f) for f in files if f.endswith(".lean")]
    if len(files) < 10:
        sys.exit(f"only {len(files)} verified proofs to sample: verdict meaningless")
    main(files)
