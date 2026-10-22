"""Reproduce one openproblems.bio leaderboard entry on our own machine (task #477, DECISIONS.md 2026-10-20): the
task's own method and metric scripts, fetched at a pinned commit and run unchanged except for their VIASH
parameter block, on the task's public data, scored against the maintainers' own results file. The gate is every
compared metric within 1%; a run that compares nothing never passes.

    python3 tools/openproblems.py reproduce --work /tmp/op --out ledger/openproblems/RUN.json
    python3 tools/openproblems.py prepare --work /tmp/op        # site-1 validation split + the reference's scores
    python3 tools/openproblems.py evolve --work /tmp/op --rounds 12 --out ledger/openproblems/evolve-RUN.jsonl

`evolve` (roadmap row 11, the bar in DECISIONS.md 2026-10-20): a free model writes predict(), each candidate runs
as the sandbox user on the validation split only, and sees the best so far and the last outcome. The test set is
never touched here. Needs anndata, scikit-learn and pyyaml; `reproduce` also needs Docker, for the task's R
correlation metric in its own image. Validation uses `metrics`, which matches the R script on the same prediction.
"""
import argparse, base64, hashlib, json, os, re, subprocess, sys, tempfile, time, urllib.request
from datetime import datetime, timezone
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]     # run with -I, which leaves the script's own folder off the path

REPO = "openproblems-bio/task_predict_modality"
S3 = "https://openproblems-data.s3.amazonaws.com/resources/task_predict_modality"
RESULTS = "run_2026-10-10_07-15-14"
DATASET = "openproblems_neurips2021/bmmc_cite/normal"
SWAP = "openproblems_neurips2021/bmmc_cite/swap"   # the other direction: the bar's check that a win is not a fit
SMOKE = ("import numpy as np\nfrom sklearn.decomposition import TruncatedSVD\nfrom sklearn.linear_model import Ridge\n\n"
         "def predict(X_train, Y_train, X_test, batch_train, batch_test):\n"
         "    svd = TruncatedSVD(32, random_state=0).fit(X_train)\n"
         "    return Ridge(alpha=1.0).fit(svd.transform(X_train), Y_train).predict(svd.transform(X_test))\n")
MAX_TEST_SCORINGS = 3                              # the bar (DECISIONS 2026-10-20): at most 3 candidates see the test set
COMPETITIVE = {"rmse": 0.6634, "mean_pearson_per_cell": 0.7857}   # guanlab_dengkw_pm, the third NeurIPS 2021 winner
NORM = "log_cp10k"                           # knnr_py's preferred_normalization (its config.vsh.yaml)
METHOD, PARAMS = "knnr_py", {"distance_method": "minkowski", "n_pcs": 50, "n_neighbors": 100}   # config defaults
METRICS = ("mse",)                          # Python, run in-process
R_METRICS = ("correlation",)                # R, run in the task's own image with its config's CRAN packages
R_IMAGE, R_CRAN = "openproblems/base_r:1", ("proxyC", "testthat", "dynutils")
TOLERANCE_PCT = 1.0
CAND_S, CAND_MEM = 1200, 13 * 2 ** 30          # a candidate's time and address space on a 16 GB runner
FILES = ("train_mod1", "train_mod2", "test_mod1", "test_mod2")


def with_par(src, par, meta):
    """The script with its VIASH block replaced by our parameters; nothing else changes."""
    return re.sub(r"## VIASH START\n.*?## VIASH END\n", lambda _: f"par = {par!r}\nmeta = {meta!r}\n", src, flags=re.S)


def with_par_r(src, par):
    """An R script with its VIASH block replaced by our parameters (as a `par <- list(...)`)."""
    args = ", ".join(f'{k} = "{v}"' for k, v in par.items())
    return re.sub(r"## VIASH START\n.*?## VIASH END\n", lambda _: f"par <- list({args})\n", src, flags=re.S)


def run_r_metric(src, data_dir, prediction, out_name):
    """The task's R metric in its own Docker image: the solution, the prediction and the output under /data."""
    d = Path(data_dir)
    (d / "metric.R").write_text(with_par_r(src, {"input_test_mod2": "/data/test_mod2.h5ad",
                                                 "input_prediction": f"/data/{Path(prediction).name}",
                                                 "output": f"/data/{out_name}"}))
    cran = ", ".join(f'\\"{p}\\"' for p in R_CRAN)
    t = time.time()
    r = subprocess.run(["docker", "run", "--rm", "-v", f"{d.resolve()}:/data", R_IMAGE, "bash", "-c",
                        f'Rscript -e "install.packages(c({cran}), repos=\\"https://cloud.r-project.org\\", quiet=TRUE)" '
                        f'>/dev/null 2>&1; Rscript /data/metric.R'], capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"R metric failed (exit {r.returncode}): {(r.stderr or r.stdout)[-1500:]}")
    return round(time.time() - t, 1)


def published(scores, dataset, method):
    """Every metric the maintainers' run scored for this method on this dataset."""
    out = {}
    for r in scores:
        if r["dataset_id"] == dataset and r["method_id"] == method:
            out.update(zip(r["metric_ids"], r["metric_values"]))
    return out


def compare(got, pub):
    metrics = {k: {"got": round(v, 4), "published": round(pub[k], 4), "diff_pct": round(100 * (v - pub[k]) / pub[k], 2)}
               for k, v in got.items() if k in pub}
    return {"metrics": metrics, "pass": bool(metrics) and all(abs(m["diff_pct"]) <= TOLERANCE_PCT for m in metrics.values())}


def knnr_chunked(X_train, Y_train, X_test, k=100, n_pcs=50, chunk=256, embed=None, random_state=None):
    """knnr_py's algorithm (an SVD of train and test together, then the mean of the k nearest training rows,
    Euclidean) with the test rows taken in chunks: on swap validation the upstream script's 14,669 x 100 x 13,953
    neighbour array would be ~82 GB. `embed` replaces the SVD in tests."""
    from sklearn.neighbors import NearestNeighbors
    if embed is None:
        from scipy.sparse import vstack, csr_matrix
        from sklearn.decomposition import TruncatedSVD
        both = vstack([csr_matrix(X_train), csr_matrix(X_test)])
        E = TruncatedSVD(n_components=min(n_pcs, both.shape[1] - 1), random_state=random_state).fit_transform(both)
        etr, ete = E[:X_train.shape[0]], E[X_train.shape[0]:]
    else:
        etr, ete = embed(X_train, X_test)
    nn = NearestNeighbors(n_neighbors=k).fit(etr)
    Y = np.asarray(Y_train, dtype=np.float32)
    out = np.empty((ete.shape[0], Y.shape[1]), dtype=np.float32)
    for i in range(0, ete.shape[0], chunk):
        idx = nn.kneighbors(ete[i:i + chunk], return_distance=False)
        out[i:i + chunk] = Y[idx].mean(axis=1)
    return out


def held_out(batches):
    """The validation cells: all of site 1, held out the way the test set holds out site 4 (DECISIONS 2026-10-20)."""
    return np.array([re.fullmatch(r"s1d\d+", b) is not None for b in batches])


def _per_cell(y, p):
    """Per cell: sum of squared errors, sum of absolute errors, Pearson (0 for a constant row)."""
    yc, pc = y - y.mean(1, keepdims=True), p - p.mean(1, keepdims=True)
    den = np.sqrt((yc ** 2).sum(1) * (pc ** 2).sum(1))
    r = np.divide((yc * pc).sum(1), den, out=np.zeros(len(y)), where=den > 0)
    return ((y - p) ** 2).sum(1), np.abs(y - p).sum(1), r


def _from_cells(sse, sae, r, n_genes):
    return {"rmse": float(np.sqrt(sse.sum() / (len(sse) * n_genes))), "mae": float(sae.sum() / (len(sae) * n_genes)),
            "mean_pearson_per_cell": float(r.mean())}


def metrics(y, p):
    """rmse and mae over every value (the mse script), mean Pearson per cell (the correlation script's)."""
    return _from_cells(*_per_cell(y, p), y.shape[1])


def paired_bootstrap(y, a, b, metric, n=10000, seed=0):
    """95% interval for metric(a) - metric(b), resampling cells with replacement, both arms on the same draw."""
    ca, cb = _per_cell(y, a), _per_cell(y, b)
    rng = np.random.default_rng(seed)
    diffs = []
    for _ in range(n):
        i = rng.integers(0, len(y), len(y))
        diffs.append(_from_cells(*(c[i] for c in ca), y.shape[1])[metric] - _from_cells(*(c[i] for c in cb), y.shape[1])[metric])
    return tuple(float(q) for q in np.percentile(diffs, [2.5, 97.5]))


# The bar's "who writes it" clause: frontier help is labeled with its drafter and reported apart. The published
# starting point in BRIEF was chosen and adapted by Claude Opus (2026-10-22, task #477), so every evolve row says so.
BRIEF_ASSIST = ("brief seeded with a published method (Guanlab-dengkw, Lance et al. 2022), chosen and adapted by "
                "Claude Opus, 2026-10-22; code written by the evolve writer")

BRIEF = """Write a Python function that predicts surface protein levels (ADT, 134 proteins) of single cells from
their RNA expression (13,953 genes), for the openproblems.bio task predict_modality (bmmc_cite, NeurIPS 2021).
Both are normalized (log CP10k for RNA). Cells come from donors at several sites; the test cells are mostly from
a site that training never sees, so batch effects between sites matter.

    def predict(X_train, Y_train, X_test, batch_train, batch_test):
        # X_train: scipy.sparse.csr_matrix (n_train x 13953) RNA;  Y_train: numpy (n_train x 134) protein
        # X_test: scipy.sparse.csr_matrix (n_test x 13953);  batch_*: numpy arrays of donor ids like "s2d4"
        # return numpy (n_test x 134) predicted protein

The same predict() is also scored the other way round (bmmc_cite/swap: protein in, 134 features, RNA out, 13,953
genes), so nothing may depend on the direction: no component count above the input's feature count (cap it,
e.g. min(50, X.shape[1] - 1)), no clipping or other assumption about the output's scale, no hard-coded shapes.
Scored by rmse over every value (lower is better) and the mean Pearson correlation per cell (higher is better).
Machine: 4 CPU cores, 16 GB RAM, no GPU, 20 minutes for the whole call. Libraries: numpy, scipy, scikit-learn
only, no internet. The reference to beat is k-nearest-neighbor regression on a 50-component TruncatedSVD of the
RNA (train and test together), 100 neighbors, which scores {ref} here.
A strong published starting point, credited: the NeurIPS 2021 GEX->ADT winner, team Guanlab-dengkw (Kaiwen
Deng; Lance et al., PMLR 176, 2022, sec. 3.2.2). The organizers report that expression scales differ by site, which
limits generalization to an unseen site; the winner's answer: truncated SVD of train and test inputs together (300
components, capped by the feature count), a z-score of each cell's row of the reduced matrix (it removes the
per-cell scale), kernel ridge regression with an RBF kernel (length scale ~10, alpha ~0.2) predicting a truncated
SVD of the output (70 components, capped), mapped back through its components; several models fit on random halves
of the training batches, then averaged. Its own code, in the swap direction (134 protein inputs), uses no input SVD
and 50 output components. Our adaptation for this machine: a kernel model on n cells needs an n x n matrix, so fit
each one on a random subset of at most 12,000 training cells (0.58 GB in float32) and average several. Improve on it if you can.
Pitfalls that crashed earlier attempts here: MultiOutputRegressor is in sklearn.multioutput and pearsonr in
scipy.stats; Ridge, RidgeCV and PLSRegression take no random_state; a sparse matrix has no .std() and
StandardScaler needs with_mean=False on it; SVR/LinearSVR and other single-output models need a wrapper for 134
outputs; never build a dense n_test x n_train matrix (14,669 x 51,506 is 5.6 GiB); keep n_neighbors <= the
number of rows it is fit on; index arrays must be integers. PLSRegression is in sklearn.cross_decomposition. In the
swap direction Y_train is a dense 51,506 x 13,953 float32 array (2.7 GiB of a 13 GiB budget): never cast it or X to
float64 or copy it whole; fit on it in place, predict in chunks of test rows, return float32. TruncatedSVD takes no
dtype argument and KernelRidge no fit_intercept. A z-score of each cell is a row operation on the dense reduced
matrix, (Z - Z.mean(axis=1, keepdims=True)) / Z.std(axis=1, keepdims=True), applied to train and test rows alike;
StandardScaler standardizes columns, not cells. Train and test have different row counts: never broadcast a
statistic computed over one set's rows against the other's.
Reply with the whole function and its imports in one ```python block."""


def extract_code(text):
    """The last ```python block that defines predict()."""
    blocks = [b for b in re.findall(r"```python\n(.*?)```", text or "", re.S) if "def predict(" in b]
    return blocks[-1] if blocks else None


SANDBOX_IMAGE, SANDBOX_MEM, STDERR_TAIL = "sb-candidate", "12g", 64 * 1024
TOOL = Path(__file__).resolve()


def docker_cmd(name, code_file, val_dir, mem=SANDBOX_MEM):
    """One candidate in its own container (2026-10-22, replacing the sandbox user): no network (the answer files are
    public), a read-only root, only this direction's inputs mounted read-only, scratch on a capped tmpfs that dies
    with it, capped memory/CPU/processes, no capabilities, gVisor when SB_RUNTIME=runsc. Its prediction comes back
    on stdout, so there is no output file to trust. SANDBOX_MEM is a budget, not a measured fit."""
    rt = os.environ.get("SB_RUNTIME")
    ro = lambda src, dst: ["--mount", f"type=bind,src={src},dst={dst},readonly"]
    # no --rm: how it ended is read first (container_exit), then docker_cleanup removes it and confirms it gone
    return ["docker", "run", "--name", name, *(["--runtime", rt] if rt else []),
            "--network", "none", "--read-only", "--tmpfs", "/tmp:rw,size=2g,mode=1777",
            "--memory", mem, "--memory-swap", mem, "--cpus", "4", "--pids-limit", "512",
            "--cap-drop", "ALL", "--security-opt", "no-new-privileges", "--log-driver", "none",
            "--user", "65534:65534", "-e", "HOME=/tmp",
            *ro(code_file, "/app/cand.py"), *ro(val_dir, "/in"), *ro(TOOL, "/app/openproblems.py"),
            SANDBOX_IMAGE, "python", "-I", "/app/openproblems.py", "run-candidate", "/app/cand.py", "/in", "-"]


CGROUP_DIRS = ("/sys/fs/cgroup/system.slice/docker-{}.scope", "/sys/fs/cgroup/docker/{}")   # systemd, cgroupfs


def container_memory(name, stop, seen):
    """While the container runs, its scope's cgroup v2 memory.peak and memory.events every 2 s, into `seen`. The scope
    goes when the container stops, so the peak is an observed lower bound (a last spike or a run under 2 s can be
    missed), and oom / oom_kill are the kernel's counts up to the last read (docs.kernel.org cgroup-v2: oom is the
    limit being hit, oom_kill a kill by any OOM killer). Diagnostic only: an unreadable cgroup leaves None."""
    cid = None
    while not stop.wait(2):
        try:
            if cid is None:
                r = subprocess.run(["docker", "inspect", "--format", "{{.Id}}", name], capture_output=True,
                                   text=True, timeout=30)
                cid = r.stdout.strip() or None
            for d in CGROUP_DIRS:
                f = Path(d.format(cid), "memory.peak") if cid else None
                if f and f.exists():
                    seen["mem_peak_gb_seen"] = round(int(f.read_text()) / 2 ** 30, 2)
                    ev = dict(l.split() for l in f.with_name("memory.events").read_text().splitlines())
                    seen.update(cgroup_oom=int(ev.get("oom", 0)), cgroup_oom_kill=int(ev.get("oom_kill", 0)))
                    break
        except (OSError, ValueError, subprocess.TimeoutExpired):
            pass


def container_exit(name):
    """Docker's record of how the container ended, read before it is removed: an observation, not a cause. Exit 137
    is any SIGKILL (the cap, the host, a timeout's kill, or the candidate's own); OOMKilled under runsc is unverified
    until the sandbox check's cap-kill and self-kill canaries show what it reports."""
    try:
        r = subprocess.run(["docker", "inspect", "--format", "{{.State.OOMKilled}} {{.State.ExitCode}}", name],
                           capture_output=True, text=True, timeout=30)
        oom, code = r.stdout.split()
        return {"oom_killed": oom == "true", "exit_code": int(code)}
    except (OSError, ValueError, subprocess.TimeoutExpired):
        return {"oom_killed": None, "exit_code": None}


def docker_cleanup(name):
    """Kill and remove the container whatever happened, then confirm it is gone. Only Docker's own "no such
    container/object" counts as gone: a daemon or API failure, or a hang, is not absence, so the job fails."""
    absent = lambda r: "no such container" in r.stderr.lower() or "no such object" in r.stderr.lower()
    try:
        rm = subprocess.run(["docker", "rm", "-f", name], capture_output=True, text=True, timeout=60)
        if rm.returncode != 0 and not absent(rm):
            raise RuntimeError(f"docker rm {name} failed: {rm.stderr[-300:]}")
        seen = subprocess.run(["docker", "inspect", name], capture_output=True, text=True, timeout=60)
    except subprocess.TimeoutExpired as e:
        raise RuntimeError(f"docker did not answer about {name}: {e}") from e
    if seen.returncode == 0 or not absent(seen):
        raise RuntimeError(f"container {name} not confirmed gone: {seen.stderr[-300:] or 'still listed'}")


def run_sandboxed(cmd, shape, timeout, cleanup):
    """Run one candidate and read its prediction: exactly 4 x prod(shape) float32 bytes on stdout (more or fewer is
    the candidate's error), stderr kept to its last 64 KiB, a hard deadline, and cleanup() always, before any
    result is used. Returns (prediction, None, stderr) or (None, why, stderr); stderr is its last 64 KiB."""
    import threading
    need = 4 * int(np.prod(shape))
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    data, tail, extra = bytearray(), bytearray(), [0]

    def read_out():
        while len(data) < need:
            chunk = proc.stdout.read(min(1 << 20, need - len(data)))
            if not chunk:
                return
            data.extend(chunk)
        extra[0] = len(proc.stdout.read(1) or b"")             # anything past the prediction

    def read_err():
        for chunk in iter(lambda: proc.stderr.read(65536), b""):
            tail.extend(chunk)
            del tail[:-STDERR_TAIL]
    readers = [threading.Thread(target=f, daemon=True) for f in (read_out, read_err)]
    for th in readers:
        th.start()
    deadline, timed_out, rc = time.monotonic() + timeout, False, None
    try:
        readers[0].join(max(0, deadline - time.monotonic()))
        timed_out = readers[0].is_alive()
        if not timed_out:
            try:
                rc = proc.wait(timeout=max(0.1, deadline - time.monotonic()))
            except subprocess.TimeoutExpired:
                timed_out = True
    finally:
        if proc.poll() is None:
            proc.kill()
        try:
            proc.wait(timeout=30)
            stuck = None
        except subprocess.TimeoutExpired as e:
            stuck = e
        cleanup()                                            # always attempted, even if the client hangs
        readers[1].join(5)
        if stuck:
            raise RuntimeError("the candidate's client did not exit after kill") from stuck
    err_text = tail.decode(errors="replace")
    why = err_text[-1500:]
    if timed_out:
        return None, f"over {timeout} s", err_text
    if rc != 0:
        return None, f"exit {rc}: {why}", err_text
    if len(data) != need or extra[0]:
        return None, f"prediction is {len(data)}{' and more' if extra[0] else ''} bytes, want {need}", err_text
    return np.frombuffer(bytes(data), dtype="<f4").reshape(shape), None, err_text


SANDBOX_CANARIES = {   # each must come back as its expected prediction: a breach makes it crash instead
    "network": ("import socket, urllib.request, numpy as np\n"
                "def predict(a, b, c, d, e):\n"
                "    for host in ('1.1.1.1', 'openproblems-data.s3.amazonaws.com'):\n"
                "        try:\n"
                "            socket.create_connection((host, 443), timeout=5).close()\n"
                "        except OSError:\n"
                "            continue\n"
                "        raise SystemExit('network reachable: ' + host)\n"
                "    return np.zeros((c.shape[0], b.shape[1]))\n"),
    "filesystem": ("import os, stat, numpy as np\n"         # only the mount can refuse: both dirs are o+w
                   "def predict(a, b, c, d, e):\n"
                   "    for d_ in ('/in', '/var/tmp'):\n"
                   "        if not os.path.isdir(d_) or not os.stat(d_).st_mode & stat.S_IWOTH:\n"
                   "            raise SystemExit('probe invalid, not world-writable: ' + d_)\n"
                   "        try:\n"
                   "            open(d_ + '/x', 'w').write('x')\n"
                   "        except OSError:\n"
                   "            continue\n"
                   "        raise SystemExit('writable: ' + d_)\n"
                   "    return np.zeros((c.shape[0], b.shape[1]))\n"),
    "scratch": ("import numpy as np\n"                    # /tmp is a 2 GiB tmpfs: 3 GiB must not fit
                "def predict(a, b, c, d, e):\n"
                "    try:\n"
                "        with open('/tmp/fill', 'wb') as f:\n"
                "            for _ in range(3 * 1024):\n"
                "                f.write(b'x' * (1 << 20))\n"
                "    except OSError as x:\n"
                "        print('scratch refused:', x)\n"
                "        return np.zeros((c.shape[0], b.shape[1]))\n"
                "    raise SystemExit('3 GiB fit in /tmp')\n"),
    "threads": ("import threading, time, numpy as np\n"   # in --memory 512m: a thread explosion must be stopped
                "hold = []\n"
                "def grab():\n"
                "    hold.append(np.ones(1 << 21, dtype=np.float32))\n"   # 8 MiB each, touched
                "    time.sleep(120)\n"
                "def predict(a, b, c, d, e):\n"
                "    print('THREADS-CANARY starting', flush=True)\n"
                "    n = 0\n"
                "    try:\n"
                "        for n in range(1, 2001):\n"
                "            threading.Thread(target=grab, daemon=True).start()\n"
                "            if n % 25 == 0:\n"
                "                print('threads started:', n, flush=True)\n"
                "    except RuntimeError as x:\n"
                "        print('THREADS-CANARY refused after', n, 'threads:', x, flush=True)\n"
                "        return np.zeros((c.shape[0], b.shape[1]))\n"
                "    time.sleep(30)\n"
                "    raise SystemExit('2000 threads holding 8 MiB each ran inside --memory 512m')\n"),
    "memory": ("import numpy as np\n"                       # run with --memory 512m: touching 1 GiB must be killed
               "def predict(a, b, c, d, e):\n"
               "    print('MEMORY-CANARY allocating 1 GiB', flush=True)\n"
               "    x = np.ones(1 << 28, dtype=np.float32)\n"
               "    return np.zeros((c.shape[0], b.shape[1])) + x[:1].sum() * 0\n"),
    "stream": ("import numpy as np\n"
               "def predict(a, b, c, d, e):\n"
               "    print('noise on stdout')\n"
               "    return np.arange(c.shape[0] * b.shape[1]).reshape(c.shape[0], b.shape[1])\n"),
}


SELF_KILL = ("import os, signal\n"                         # exit 137 with no memory pressure at all
             "def predict(a, b, c, d, e):\n"
             "    os.kill(os.getpid(), signal.SIGKILL)\n")


def sandbox_check(work):
    """Before any real candidate: the container has no network, cannot write where it should not, and streams a
    prediction back exactly. Raises on any failure, so the job stops before a shot or a round is spent."""
    from scipy import sparse
    inp = Path(work) / "sandbox-check"
    write_inputs(inp, sparse.csr_matrix(np.ones((6, 4))), np.ones((6, 3)), sparse.csr_matrix(np.ones((5, 4))),
                 np.array(["s1d1"] * 6), np.array(["s2d1"] * 5))
    zeros = np.zeros((5, 3))
    want = {"network": zeros, "filesystem": zeros, "scratch": zeros, "threads": "killed or refused", "memory": "killed",
            "stream": np.arange(15.0).reshape(5, 3)}
    for name, code in SANDBOX_CANARIES.items():
        f = Path(work) / f"canary-{name}.py"
        f.write_text(code)
        p, err, seen = sandboxed_predict(f, inp, (5, 3), 300, dir_mode=0o777 if name == "filesystem" else 0o755,
                                         mem="512m" if name in ("memory", "threads") else SANDBOX_MEM)
        killed = p is None and (err or "").startswith("exit 137")
        expect = want[name] if isinstance(want[name], str) else None
        if expect == "killed":                   # reached the allocation, then SIGKILLed (exit 137)
            if not (killed and "MEMORY-CANARY allocating" in seen):
                raise SystemExit(f"sandbox check {name} failed: want a SIGKILL after the allocation began, got "
                                 f"{'a prediction' if p is not None else err[:300]}")
        elif expect == "killed or refused":      # the memory cap stopped it, or thread creation was refused
            refused = p is not None and np.array_equal(p, zeros) and "THREADS-CANARY refused after" in seen
            if not ("THREADS-CANARY starting" in seen and (killed or refused)):
                raise SystemExit(f"sandbox check {name} failed: want killed (exit 137) or refused after starting, got "
                                 f"{'a prediction' if p is not None else (err or '')[:300]}")
        elif err or not np.array_equal(p, want[name]):
            raise SystemExit(f"sandbox check {name} failed: {err or 'wrong prediction'}")
        lines = [l for l in seen.splitlines() if l.strip()]
        print(f"sandbox check {name}: ok  [{err[:60] if err else (lines[-1][:160] if lines else 'no output')}]", flush=True)
    for name, code, mem in (("cap kill", SANDBOX_CANARIES["memory"], "512m"), ("self kill", SELF_KILL, SANDBOX_MEM)):
        f = Path(work) / f"diag-{name.replace(' ', '-')}.py"         # reported, not gated: what a known kill looks like
        f.write_text(code)
        diag = {}
        _, err, _ = sandboxed_predict(f, inp, (5, 3), 300, mem=mem, diag=diag)
        print(f"sandbox diagnostics, {name}: {(err or 'no error')[:40]!r} {json.dumps(diag)}", flush=True)
    return 0


def _swap_ok(m, ref):
    """No worse than the reference on the swap direction too, when the reference has one (2026-10-21 on)."""
    if "swap" not in ref:
        return True
    s = m.get("swap")
    return bool(s) and s["rmse"] <= ref["swap"]["rmse"] and s["mean_pearson_per_cell"] >= ref["swap"]["mean_pearson_per_cell"]


def gate_ci(y, p, ref_pred, n=2000):
    """The bar's paired bootstrap (candidate minus reference), on the validation cells: a point lead is not enough
    (shot 1, 2026-10-21: +0.002 Pearson on validation, -0.020 on test)."""
    return {m: [round(x, 5) for x in paired_bootstrap(y, p, ref_pred, m, n=n)] for m in ("rmse", "mean_pearson_per_cell")}


def _ci_ok(m, ref):
    """When the reference carries validation predictions (2026-10-22 on), both intervals must clear zero, as on test."""
    if not ref.get("bootstrap"):
        return True
    ci = m.get("ci")
    return bool(ci) and ci["rmse"][1] < 0 and ci["mean_pearson_per_cell"][0] > 0


def best(rows, ref):
    """The largest validation Pearson-per-cell lead among candidates better than the reference on rmse and Pearson
    (the bar's own pair), no worse on swap, and, with a validation bootstrap, clear of zero on both. Ranked by
    Pearson since 2026-10-22: ranked by rmse, shot 1 won rmse on test and lost Pearson (our hypothesis, not
    established: shrinkage toward the mean lowers rmse and flattens correlation); rmse breaks ties."""
    ok = [r for r in rows if "metrics" in r and r["metrics"]["mean_pearson_per_cell"] > ref["mean_pearson_per_cell"]
          and r["metrics"]["rmse"] < ref["rmse"] and _swap_ok(r["metrics"], ref) and _ci_ok(r["metrics"], ref)]
    return max(ok, key=lambda r: (r["metrics"]["mean_pearson_per_cell"], -r["metrics"]["rmse"])) if ok else None


def failed_checks(m, ref):
    """Which of best()'s checks a candidate's validation metrics fail, in words the writer can act on."""
    out = []
    if not m["rmse"] < ref["rmse"]:
        out.append("rmse below the reference's")
    if not m["mean_pearson_per_cell"] > ref["mean_pearson_per_cell"]:
        out.append("Pearson per cell above the reference's")
    if not _swap_ok(m, ref):
        out.append("no worse than the reference on the swap direction")
    if not _ci_ok(m, ref):
        out.append("both leads clear of zero in the validation bootstrap")
    return out


def best_or_closest(rows, ref):
    """The best candidate by the bar's rule, else the highest validation Pearson among those that ran (rmse breaks
    ties), the same order best() uses."""
    ran = [r for r in rows if "metrics" in r and r.get("code")]
    return best(ran, ref) or (max(ran, key=lambda r: (r["metrics"]["mean_pearson_per_cell"], -r["metrics"]["rmse"]))
                              if ran else None)


def _fmt(m):
    s = f"rmse {m['rmse']:.4f}, mean Pearson per cell {m['mean_pearson_per_cell']:.4f}"
    if m.get("swap"):
        s += f"; swap direction: rmse {m['swap']['rmse']:.4f}, mean Pearson per cell {m['swap']['mean_pearson_per_cell']:.4f}"
    return s


def both_ways(score_normal, score_swap):
    """A candidate scored on the normal direction, then the swap direction; a crash either way is an error that
    says which way (with the normal scores, if it got that far), so the writer can fix it."""
    def score(code):
        r = score_normal(code)
        if "error" in r:
            return {"error": "normal direction: " + r["error"]}
        s = score_swap(code)
        if "error" in s:
            return {"error": f"normal direction ran ({_fmt(r)}); swap direction crashed: " + s["error"]}
        return {**r, "swap": s}
    return score


def evolve(rounds, ask, score, ref, writer, seed=None):
    """`rounds` asks; each sees the best candidate so far (from `seed`, the best of earlier runs, until this run
    beats it) with its validation scores, and the last outcome. score(code) -> metrics, or {"error": why}. Every
    attempt is a row; the seed is context, not a row."""
    rows = []
    for i in range(rounds):
        prompt = BRIEF.format(ref=_fmt(ref))
        top = best_or_closest(rows + ([seed] if seed else []), ref)
        if top:          # the closest so far, shown even below the reference's Pearson (run 39519234354: 3 ran, none at it)
            standing = ("the best so far, past every check" if best([top], ref)
                        else f"the closest so far; it does not yet pass: {', '.join(failed_checks(top['metrics'], ref))}")
            prompt += (f"\n\nThis is {standing}: {_fmt(top['metrics'])}. Beat the reference on both:"
                       f"\n```python\n{top['code']}```")
        if rows:
            last = rows[-1]
            if "error" in last and last.get("code"):       # a crash comes back with its code, to be fixed, not rewritten
                prompt += f"\n\nThe last attempt crashed. Its code:\n```python\n{last['code']}```\nThe error: {last['error'][-1500:]}"
            elif "error" in last:
                prompt += "\n\nThe last attempt failed: " + last["error"][-1500:]
            elif last is not top:
                prompt += f"\n\nThe last attempt scored {_fmt(last['metrics'])}."
        t = time.time()
        reply = ask(prompt)
        row = {"round": i, "writer": writer, "ask_s": round(time.time() - t, 1), "brief_assist": BRIEF_ASSIST}
        code = extract_code(reply) if isinstance(reply, str) else None
        if code is None:
            row["error"] = "no code in the reply" if isinstance(reply, str) else f"no reply: {reply.get('error')}"
        else:
            r = score(code)
            row.update(code=code, **({"error": r["error"]} if "error" in r else {"metrics": r}))
        rows.append(row)
        print(json.dumps({k: v for k, v in row.items() if k != "code"})[:400], flush=True)
    return rows


def verdict(normal, swap):
    """The pre-registered bar. normal: metric -> {cand, ref, ci} (ci: 95% interval of cand - ref over the test cells);
    swap: {cand, ref} metric dicts. Useful: better than the reference on both metrics with each interval clear of
    zero, and no worse on swap. Competitive: among the winners on normal; reported, not the bar."""
    rmse, pear = normal["rmse"], normal["mean_pearson_per_cell"]
    swap_ok = (swap["cand"]["rmse"] <= swap["ref"]["rmse"]
               and swap["cand"]["mean_pearson_per_cell"] >= swap["ref"]["mean_pearson_per_cell"])
    return {"useful": rmse["ci"][1] < 0 and pear["ci"][0] > 0 and swap_ok, "swap_no_worse": swap_ok,
            "competitive": rmse["cand"] <= COMPETITIVE["rmse"] and pear["cand"] >= COMPETITIVE["mean_pearson_per_cell"]}


QUALIFY_MEM = "10g"      # under the 12g default: the host holds the loaded layers and the fold's answers meanwhile
QUALIFY_POLICY = ("loso-v1 (2026-10-22): every training site held out in turn, both directions; the candidate must beat "
                  "knnr_chunked (random_state 0) on that site on rmse (lower) and Pearson per cell (higher), every site, "
                  "no execution error; mean and worst-site deltas reported")


def sites_of(batches):
    """The training sites, from batch names like s2d4; any other name stops qualification (the folds must be real)."""
    sites = set()
    for b in batches:
        m = re.fullmatch(r"s(\d+)d\d+", str(b))
        if not m:
            raise ValueError(f"batch {b!r} is not s<site>d<donor>")
        sites.add(int(m.group(1)))
    return sorted(sites)


def qualify_verdict(rows):
    """Passed only if there are sites and every one ran and won on both metrics, strictly."""
    ok = bool(rows) and all(r.get("error") is None and r["cand"]["rmse"] < r["ref"]["rmse"]
                            and r["cand"]["mean_pearson_per_cell"] > r["ref"]["mean_pearson_per_cell"] for r in rows)
    d = [r["cand"]["mean_pearson_per_cell"] - r["ref"]["mean_pearson_per_cell"] for r in rows if r.get("error") is None]
    return {"passed": ok, "sites": len(rows), "mean_pearson_delta": float(np.mean(d)) if d else None,
            "worst_pearson_delta": float(min(d)) if d else None}


def qualify_direction(X, Y, batches, work, code_file, predict=None, reference=None):
    """Each training site held out in turn: the reference and the candidate (in its container) on that site."""
    import shutil
    predict = predict or sandboxed_predict
    reference = reference or (lambda a, b, c: knnr_chunked(a, b, c, random_state=0))
    import resource
    rows = []
    for s in sites_of(batches):
        t0 = time.monotonic()
        v = np.array([re.fullmatch(rf"s{s}d\d+", str(b)) is not None for b in batches])
        inp = Path(work) / f"site{s}" / "in"
        write_inputs(inp, X[~v], Y[~v], X[v], batches[~v], batches[v])
        y = _dense(Y[v]).astype(np.float32)
        ref = metrics(y, np.asarray(reference(X[~v], _dense(Y[~v]).astype(np.float32), X[v])))
        diag = {}
        p, err, _ = predict(code_file, inp, y.shape, CAND_S + 60, mem=QUALIFY_MEM, diag=diag)
        if err is None and not np.isfinite(p).all():
            err = "non-finite values in the prediction"
        rows.append({"site": s, "n_train": int((~v).sum()), "n_held": int(v.sum()), "error": err,
                     "cand": None if err else {k: round(x, 4) for k, x in metrics(y, p).items()},
                     "ref": {k: round(x, 4) for k, x in ref.items()},
                     "seconds": round(time.monotonic() - t0, 1),           # measured, for the runner's budget
                     "host_peak_rss_gb": round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 20, 2),
                     "container": diag})                  # its own peak and how it ended (2026-10-22: swap site 3, exit 137)
        del p, y                                     # nothing of this fold is held while the next one runs
        shutil.rmtree(inp.parent, ignore_errors=True)
        print(f"qualify site {s}: {rows[-1]['cand'] or err} vs {rows[-1]['ref']}", flush=True)
    return rows


def write_receipt(out, source, code, rows_by_direction, expected=None):
    """`expected`: the sites discovered in each direction's training data, so a receipt missing a fold can be seen."""
    allrows = [r for rows in rows_by_direction.values() for r in rows]
    expected = expected or {d: [r["site"] for r in rows] for d, rows in rows_by_direction.items()}
    receipt = {"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "policy": QUALIFY_POLICY,
               "source": source, "code_sha": hashlib.sha256(code.encode()).hexdigest(), "rows": rows_by_direction,
               "expected_sites": expected, "verdict": qualify_verdict(allrows)}
    Path(out).write_text(json.dumps(receipt, indent=1) + "\n")
    return receipt


def receipt_complete(r):
    """Both directions, each with exactly the sites its training data has (the same sites both ways)."""
    rows, exp = r.get("rows") or {}, r.get("expected_sites") or {}
    if set(rows) != {"normal", "swap"} or set(exp) != {"normal", "swap"} or sorted(exp["normal"]) != sorted(exp["swap"]):
        return False
    return all(exp[d] and sorted(x["site"] for x in rows[d]) == sorted(exp[d]) for d in rows)


def check_qualified(ledger_dir, source, code):
    """A test scoring only for a candidate whose exact code passed qualification under today's policy; the verdict
    is recomputed from the receipt's rows, never taken from its own field."""
    sha = hashlib.sha256(code.encode()).hexdigest()
    for f in sorted(Path(ledger_dir).glob("qualify-*.json")):
        r = json.loads(f.read_text())
        if r.get("source") == source and r.get("code_sha") == sha and r.get("policy") == QUALIFY_POLICY:
            if receipt_complete(r) and qualify_verdict([x for rows in r["rows"].values() for x in rows])["passed"]:
                return f
    sys.exit("no passing leave-one-site-out receipt for this candidate's exact code (run openproblems_qualify)")


def qualify(work, code, source, out):
    """Leave-one-site-out on the training data only (the test files are never downloaded here), both directions."""
    import anndata as ad
    Path(work).mkdir(parents=True, exist_ok=True)
    code_file = Path(work) / "qualify-cand.py"
    code_file.write_text(code)
    rows, expected = {}, {}
    for name, ds in (("normal", DATASET), ("swap", SWAP)):
        data = Path(work) / f"q-{name}"
        download(data, ds, files=("train_mod1", "train_mod2"))
        m1, m2 = (ad.read_h5ad(data / f"{f}.h5ad") for f in ("train_mod1", "train_mod2"))
        b = m1.obs["batch"].astype(str).values
        expected[name] = sites_of(b)
        rows[name] = qualify_direction(m1.layers["normalized"], m2.layers["normalized"], b,
                                       Path(work) / f"q-{name}-folds", code_file)
        del m1, m2
    r = write_receipt(out, source, code, rows, expected)
    print(json.dumps({"source": source, "verdict": r["verdict"]}), flush=True)
    return 0


def shots_used(ledger_dir):
    """Runs that reserved or spent a test scoring: a reservation (shot-<run>.json) is published before the test set
    is read, so a run lost mid-scoring still counts (2026-10-22: before, only a finished final-<run>.json did)."""
    return len({p.stem.split("-", 1)[1] for pat in ("final-*.json", "shot-*.json") for p in Path(ledger_dir).glob(pat)})


def shot_left(ledger_dir):
    return shots_used(ledger_dir) < MAX_TEST_SCORINGS


def reserve(ledger_dir, run_id, source, code):
    """Take one of the test scorings for this run and this exact candidate, before any test data is read; only a
    candidate that passed leave-one-site-out under today's policy can take one."""
    check_qualified(ledger_dir, source, code)
    if not shot_left(ledger_dir):
        sys.exit(f"{MAX_TEST_SCORINGS} candidates have already seen the test set (the bar's limit)")
    f = Path(ledger_dir) / f"shot-{run_id}.json"
    f.write_text(json.dumps({"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "run": run_id,
                             "source": source, "code_sha": hashlib.sha256(code.encode()).hexdigest()}, indent=1) + "\n")
    return f


def check_reservation(out, source, code):
    """final() reads the test set only under its own run's reservation for this candidate's exact code."""
    run = Path(out).stem.split("-", 1)[1]
    f = Path(out).parent / f"shot-{run}.json"
    if not f.exists():
        sys.exit(f"no reservation {f.name}: reserve the shot (and publish it) before scoring")
    r = json.loads(f.read_text())
    if r.get("source") != source or r.get("code_sha") != hashlib.sha256(code.encode()).hexdigest():
        sys.exit(f"{f.name} reserves a different candidate")


def candidate_from(ledger_file, round_no):
    """A candidate's code, as its evolve row recorded it; only a candidate that ran on validation qualifies."""
    for line in Path(ledger_file).read_text().splitlines():
        r = json.loads(line)
        if r.get("round") == round_no:
            if "metrics" not in r or not r.get("code"):
                raise ValueError(f"round {round_no} did not run on validation")
            return r["code"]
    raise ValueError(f"no round {round_no} in {ledger_file}")


def fetch_script(path, sha):
    raw = subprocess.run(["gh", "api", f"repos/{REPO}/contents/{path}?ref={sha}", "-q", ".content"],
                         capture_output=True, text=True, check=True).stdout
    return base64.b64decode(raw).decode()


def run_script(src, name, par, meta):
    t = time.time()
    exec(compile(with_par(src, par, meta), name, "exec"), {"__name__": "__main__"})
    return round(time.time() - t, 1)


def _dense(a):
    from scipy import sparse
    return a.toarray() if sparse.issparse(a) else np.asarray(a)


def write_inputs(d, X_train, Y_train, X_test, batch_train, batch_test):
    """What a candidate's predict() is given, laid out for run_candidate; readable by the sandbox user."""
    from scipy import sparse
    d.mkdir(parents=True, exist_ok=True)
    sparse.save_npz(d / "X_train.npz", sparse.csr_matrix(X_train))
    np.save(d / "Y_train.npy", _dense(Y_train).astype(np.float32))
    sparse.save_npz(d / "X_test.npz", sparse.csr_matrix(X_test))
    np.save(d / "batch_train.npy", np.asarray(batch_train))
    np.save(d / "batch_test.npy", np.asarray(batch_test))


def prepare(data, val, answers):
    """Validation arrays (all of site 1 held out) where the sandbox can read them, the answers where it cannot,
    and the reference's validation scores from the task's own knnr_py script."""
    import anndata as ad
    m1, m2 = ad.read_h5ad(data / "train_mod1.h5ad"), ad.read_h5ad(data / "train_mod2.h5ad")
    v = held_out(m1.obs["batch"].astype(str).values)
    answers.mkdir(parents=True, exist_ok=True)
    dense = _dense
    b = m1.obs["batch"].astype(str).values
    write_inputs(val, m1.layers["normalized"][~v], m2.layers["normalized"][~v], m1.layers["normalized"][v], b[~v], b[v])
    y_val = dense(m2.layers["normalized"][v]).astype(np.float32)
    np.save(answers / "Y_val.npy", y_val)
    h5 = answers / "h5"
    h5.mkdir(exist_ok=True)
    m1[~v].write_h5ad(h5 / "train_mod1.h5ad"); m2[~v].write_h5ad(h5 / "train_mod2.h5ad"); m1[v].write_h5ad(h5 / "test_mod1.h5ad")
    sha = subprocess.run(["gh", "api", f"repos/{REPO}/commits/main", "-q", ".sha"], capture_output=True, text=True,
                         check=True).stdout.strip()
    run_script(fetch_script(f"src/methods/{METHOD}/script.py", sha), METHOD,
               {"input_train_mod1": str(h5 / "train_mod1.h5ad"), "input_train_mod2": str(h5 / "train_mod2.h5ad"),
                "input_test_mod1": str(h5 / "test_mod1.h5ad"), "output": str(h5 / "ref.h5ad"), **PARAMS}, {"name": METHOD})
    ref_pred = dense(ad.read_h5ad(h5 / "ref.h5ad").layers["normalized"]).astype(np.float32)
    np.save(answers / "ref_pred.npy", ref_pred)                  # the validation bootstrap's other arm
    ref = {**metrics(y_val, ref_pred), "bootstrap": True}
    (answers / "ref.json").write_text(json.dumps(ref))
    return ref


def prepare_swap(data, val, answers):
    """The swap direction's validation split (site 1 held out, as in prepare) and the reference's scores there,
    from knnr_chunked: the upstream script would need ~82 GB on 14,669 held-out cells x 13,953 genes. Its chunked
    twin matched the published knnr_py on the normal test set (rmse +0.10%, Pearson +0.01%, 2026-10-21)."""
    import anndata as ad
    m1, m2 = ad.read_h5ad(data / "train_mod1.h5ad"), ad.read_h5ad(data / "train_mod2.h5ad")
    b = m1.obs["batch"].astype(str).values
    v = held_out(b)
    answers.mkdir(parents=True, exist_ok=True)
    y_train = _dense(m2.layers["normalized"][~v]).astype(np.float32)
    write_inputs(val, m1.layers["normalized"][~v], y_train, m1.layers["normalized"][v], b[~v], b[v])
    y_val = _dense(m2.layers["normalized"][v]).astype(np.float32)
    np.save(answers / "Y_val.npy", y_val)
    ref = metrics(y_val, knnr_chunked(m1.layers["normalized"][~v], y_train, m1.layers["normalized"][v]))
    (answers / "ref.json").write_text(json.dumps(ref))
    return ref


def run_candidate(code_file, val, out):
    """Inside the sandbox: one candidate's predict() on the inputs. With out "-" its prediction is the only thing on
    stdout (raw float32, row-major); the candidate's own prints go to stderr, moved there before its code runs."""
    from scipy import sparse
    data = None
    if out == "-":
        data = os.fdopen(os.dup(1), "wb")
        os.dup2(2, 1)
        sys.stdout = sys.stderr
    ns = {"__name__": "candidate"}
    exec(compile(Path(code_file).read_text(), "candidate.py", "exec"), ns)
    val = Path(val)
    y = ns["predict"](sparse.load_npz(val / "X_train.npz"), np.load(val / "Y_train.npy"), sparse.load_npz(val / "X_test.npz"),
                      np.load(val / "batch_train.npy", allow_pickle=True), np.load(val / "batch_test.npy", allow_pickle=True))
    arr = np.ascontiguousarray(y, dtype="<f4")
    if data:
        data.write(arr.tobytes())
        data.flush()
    else:
        np.save(out, arr)


def scorer(val, answers, work):
    """Score one direction's candidates on its validation split, each in its own container (docker_cmd)."""
    import uuid
    y_val = np.load(answers / "Y_val.npy")
    n = [0]

    def score(code):
        n[0] += 1
        code_file = work / f"cand{n[0]}.py"
        code_file.write_text(code)
        p, err, _ = sandboxed_predict(code_file, val, y_val.shape, CAND_S + 60)
        if err:
            return {"error": err}
        if not np.isfinite(p).all():
            return {"error": "non-finite values in the prediction"}
        m = {k: round(v, 4) for k, v in metrics(y_val, p).items()}
        if ref_pred is not None:
            m["ci"] = gate_ci(y_val, p, ref_pred)
        return m
    ref_file = answers / "ref_pred.npy"
    ref_pred = np.load(ref_file) if ref_file.exists() else None
    return score


def sandboxed_predict(code_file, inputs, shape, timeout, dir_mode=0o755, mem=SANDBOX_MEM, diag=None):
    """A candidate's prediction from its own container; the inputs and its code made readable to the container's
    user (only the inputs directory is mounted, so nothing else needs to be). `diag`, if given, gets the
    container's observed memory peak, cgroup OOM counts, OOMKilled and exit code: evidence for a kill, not its cause."""
    import threading, uuid
    for f in [inputs, *Path(inputs).iterdir()]:
        os.chmod(f, dir_mode if Path(f).is_dir() else 0o644)
    os.chmod(code_file, 0o644)
    name = f"sb-cand-{uuid.uuid4().hex[:12]}"
    seen, stop = {"mem_peak_gb_seen": None, "cgroup_oom": None, "cgroup_oom_kill": None}, threading.Event()
    sampler = threading.Thread(target=container_memory, args=(name, stop, seen), daemon=True)
    sampler.start()

    def cleanup():
        try:
            stop.set()
            sampler.join(35)
            seen.update(container_exit(name))
        finally:                                             # no diagnostic may stand between it and its removal
            docker_cleanup(name)
    try:
        return run_sandboxed(docker_cmd(name, Path(code_file).resolve(), Path(inputs).resolve(), mem), shape,
                             timeout, cleanup)
    finally:
        if diag is not None:
            diag.update(seen, mem_cap=mem)


def writer_ask(lane):
    """Leanstral (Mistral's Labs API, the free key) by default, or any Kumori router lane."""
    if lane == "leanstral":
        import leanstral
        key = leanstral.key_from_env()
        pacer = leanstral.Pacer(leanstral.MIN_GAP_S)

        def ask(prompt):
            try:
                return leanstral.reply(leanstral.call_prompt(key, prompt, pacer))
            except Exception as e:
                return {"error": f"{type(e).__name__}: {str(e)[:160]}"}
        return ask, f"leanstral ({leanstral.MODEL})"
    import decompose
    return decompose.router_ask(lane)[0], f"router lane {lane}"


def download(data, dataset=DATASET, files=FILES):
    data.mkdir(parents=True, exist_ok=True)
    for f in files:
        if not (data / f"{f}.h5ad").exists():
            urllib.request.urlretrieve(f"{S3}/datasets/{dataset}/{NORM}/{f}.h5ad", data / f"{f}.h5ad")


def pinned_sha():
    return subprocess.run(["gh", "api", f"repos/{REPO}/commits/main", "-q", ".sha"], capture_output=True, text=True,
                          check=True).stdout.strip()


def reproduce(work, out):
    import anndata as ad, yaml
    data, sha, pred = work / "data", pinned_sha(), str(work / "prediction.h5ad")
    download(data)
    seconds = {METHOD: run_script(fetch_script(f"src/methods/{METHOD}/script.py", sha), METHOD,
                                  {"input_train_mod1": str(data / "train_mod1.h5ad"),
                                   "input_train_mod2": str(data / "train_mod2.h5ad"),
                                   "input_test_mod1": str(data / "test_mod1.h5ad"), "output": pred, **PARAMS},
                                  {"name": METHOD})}
    got = {}
    for m in METRICS:
        score_file = str(work / f"score_{m}.h5ad")
        seconds[m] = run_script(fetch_script(f"src/metrics/{m}/script.py", sha), m,
                                {"input_test_mod2": str(data / "test_mod2.h5ad"), "input_prediction": pred,
                                 "output": score_file}, {"name": m})
        u = ad.read_h5ad(score_file).uns
        got.update(zip(u["metric_ids"], map(float, u["metric_values"])))
    import shutil
    shutil.copy(pred, data / "prediction.h5ad")
    for m in R_METRICS:
        seconds[m] = run_r_metric(fetch_script(f"src/metrics/{m}/script.R", sha), data, data / "prediction.h5ad",
                                  f"score_{m}.h5ad")
        u = ad.read_h5ad(data / f"score_{m}.h5ad").uns
        got.update(zip(u["metric_ids"], map(float, u["metric_values"])))
    with urllib.request.urlopen(f"{S3}/results/{RESULTS}/score_uns.yaml") as r:
        pub = published(yaml.safe_load(r.read()), DATASET, METHOD)
    row = {"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "task": REPO, "commit": sha,
           "results": RESULTS, "dataset": DATASET, "normalization": NORM, "method": METHOD, "params": PARAMS,
           "metrics_run": list(METRICS) + [f"{m} (R, {R_IMAGE})" for m in R_METRICS], "tolerance_pct": TOLERANCE_PCT, "seconds": seconds, **compare(got, pub)}
    print(json.dumps(row, indent=1))
    if out:
        Path(out).parent.mkdir(parents=True, exist_ok=True)
        Path(out).write_text(json.dumps(row) + "\n")
    return 0 if row["pass"] else 1


def official(sha, data, prediction):
    """The task's own scores for one prediction: its mse script in-process, its R correlation script in its image."""
    import anndata as ad
    tag = Path(prediction).stem
    run_script(fetch_script("src/metrics/mse/script.py", sha), "mse",
               {"input_test_mod2": str(data / "test_mod2.h5ad"), "input_prediction": str(prediction),
                "output": str(data / f"mse-{tag}.h5ad")}, {"name": "mse"})
    run_r_metric(fetch_script("src/metrics/correlation/script.R", sha), data, prediction, f"corr-{tag}.h5ad")
    got = {}
    for f in (f"mse-{tag}.h5ad", f"corr-{tag}.h5ad"):
        u = ad.read_h5ad(data / f).uns
        got.update(zip(u["metric_ids"], [round(float(v), 4) for v in u["metric_values"]]))
    return got


def final(work, code, source, out):
    """One candidate on the test set, both directions, scored and judged by the bar. The answers stay unreadable
    to the candidate; the reference is the task's own knnr_py, re-run here."""
    import anndata as ad
    from scipy.sparse import csc_matrix
    if source != "smoke":
        check_qualified(Path(out).parent, source, code)
        check_reservation(out, source, code)
    sha, res = pinned_sha(), {}
    cand_dir = work / "candidates"
    cand_dir.mkdir(parents=True, exist_ok=True)
    for name, ds in (("normal", DATASET), ("swap", SWAP)):
        data, inp = work / f"final-{name}" / "data", work / f"final-{name}" / "in"
        download(data, ds)
        data.chmod(0o700)                                          # the answers: not the sandbox user's to read
        m1, m2, t1, t2 = (ad.read_h5ad(data / f"{f}.h5ad") for f in FILES)
        write_inputs(inp, m1.layers["normalized"], m2.layers["normalized"], t1.layers["normalized"],
                     m1.obs["batch"].astype(str).values, t1.obs["batch"].astype(str).values)
        dataset_id, var = m1.uns["dataset_id"], m2.var
        del m1, m2                                                   # the 3.7 GB RNA side of swap: not held below
        for p in [inp, *inp.iterdir()]:
            p.chmod(0o755 if p.is_dir() else 0o644)
        if name == "normal":            # the bootstrap needs knnr_py's own predictions, so it is re-run here
            run_script(fetch_script(f"src/methods/{METHOD}/script.py", sha), METHOD,
                       {"input_train_mod1": str(data / "train_mod1.h5ad"), "input_train_mod2": str(data / "train_mod2.h5ad"),
                        "input_test_mod1": str(data / "test_mod1.h5ad"), "output": str(data / "ref.h5ad"), **PARAMS},
                       {"name": METHOD})
        code_file = cand_dir / f"final-{name}.py"
        code_file.write_text(code)
        y = _dense(t2.layers["normalized"]).astype(np.float32)
        p, err, _ = sandboxed_predict(code_file, inp, y.shape, CAND_S + 120)   # only this direction's inputs mounted
        if err:
            res[name] = {"error": err}
            continue
        if not np.isfinite(p).all():
            res[name] = {"error": "non-finite values in the prediction"}
            continue
        ad.AnnData(layers={"normalized": csc_matrix(p)}, obs=t1.obs, var=var,
                   uns={"dataset_id": dataset_id, "method_id": "sparebrains_candidate"}).write_h5ad(data / "cand.h5ad")
        if name == "normal":
            ref = _dense(ad.read_h5ad(data / "ref.h5ad").layers["normalized"]).astype(np.float32)
            res[name] = {"cand": official(sha, data, data / "cand.h5ad"), "ref": official(sha, data, data / "ref.h5ad"),
                         "_y": y, "_p": p, "_r": ref}
        else:                           # swap compares scores only: knnr_py's published run is the reference (a fresh
            import yaml                 # one needs ~10 GB, past a 16 GB runner beside the candidate; ours matched
            with urllib.request.urlopen(f"{S3}/results/{RESULTS}/score_uns.yaml") as r:   # published within 0.2%)
                ref_scores = published(yaml.safe_load(r.read()), ds, METHOD)
            res[name] = {"cand": official(sha, data, data / "cand.h5ad"),
                         "ref": {k: round(float(v), 4) for k, v in ref_scores.items()}, "ref_source": f"published {RESULTS}"}
    row = {"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "task": REPO, "commit": sha,
           "source": source, "code": code, "normalization": NORM}
    if any("error" in v for v in res.values()):
        row.update(verdict={"useful": False, "competitive": False}, errors={k: v["error"] for k, v in res.items() if "error" in v})
    else:
        n = res["normal"]
        normal = {m: {"cand": n["cand"][m], "ref": n["ref"][m],
                      "ci": [round(x, 5) for x in paired_bootstrap(n["_y"], n["_p"], n["_r"], m)]}
                  for m in ("rmse", "mean_pearson_per_cell")}
        row.update(normal={"scores": {"cand": n["cand"], "ref": n["ref"]}, "bootstrap": normal},
                   swap={"scores": {"cand": res["swap"]["cand"], "ref": res["swap"]["ref"]},
                         "ref_source": res["swap"].get("ref_source")},
                   verdict=verdict(normal, {"cand": res["swap"]["cand"], "ref": res["swap"]["ref"]}))
    Path(out).write_text(json.dumps(row, indent=1) + "\n")
    if source == "smoke" and "errors" in row:              # the smoke proves the pipeline: it must run both ways
        sys.exit(f"smoke failed: {row['errors']}")
    print(json.dumps({k: row[k] for k in ("source", "verdict")} | ({"normal": row["normal"]["bootstrap"]} if "normal" in row else {"errors": row.get("errors")})), flush=True)
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["reproduce", "prepare", "evolve", "run-candidate", "reserve", "final", "sandbox-check",
                                   "qualify"])
    ap.add_argument("--evolve-file", help="final: the evolve ledger holding the candidate")
    ap.add_argument("--round", type=int, help="final: the candidate's round in that file")
    ap.add_argument("--smoke", action="store_true", help="final: a fixed, trusted ridge candidate; proves the pipeline, "
                                                          "is not one of the bar's 3 test scorings, and is not published")
    ap.add_argument("args", nargs="*", help="run-candidate: CODE VAL_DIR OUT (inside the sandbox)")
    ap.add_argument("--work", help="scratch: data/, val/ (sandbox-readable), answers/ (not), candidates/")
    ap.add_argument("--out", help="the ledger file to write")
    ap.add_argument("--rounds", type=int, default=12)
    ap.add_argument("--lane", default="leanstral")
    a = ap.parse_args()
    if a.cmd == "run-candidate":
        run_candidate(*a.args)
        return 0
    if a.cmd == "sandbox-check":
        return sandbox_check(Path(a.work or tempfile.mkdtemp()))
    if a.cmd == "qualify":
        return qualify(Path(a.work), candidate_from(a.evolve_file, a.round), {"evolve_file": a.evolve_file, "round": a.round},
                       a.out)
    if a.cmd == "reserve":                  # --out names the final-<run>.json this reservation is for
        run = Path(a.out).stem.split("-", 1)[1]
        f = reserve(Path(a.out).parent, run, {"evolve_file": a.evolve_file, "round": a.round},
                    candidate_from(a.evolve_file, a.round))
        print(f"reserved {f.name}: {shots_used(f.parent)} of {MAX_TEST_SCORINGS} test scorings taken", flush=True)
        return 0
    work = Path(a.work)
    if a.cmd == "reproduce":
        return reproduce(work, a.out)
    if a.cmd == "final":
        if a.smoke:
            return final(work, SMOKE, "smoke", a.out)
        code = candidate_from(a.evolve_file, a.round)
        return final(work, code, {"evolve_file": a.evolve_file, "round": a.round}, a.out)
    val, answers = work / "val", work / "answers"
    if a.cmd == "prepare":
        download(work / "data")
        ref = prepare(work / "data", val, answers)
        download(work / "data-swap", SWAP)
        ref["swap"] = prepare_swap(work / "data-swap", work / "val-swap", work / "answers-swap")
        print(json.dumps({"reference_on_validation": ref}))
        return 0
    ref = json.loads((answers / "ref.json").read_text())
    ref["swap"] = json.loads((work / "answers-swap" / "ref.json").read_text())
    cand = work / "candidates"
    cand.mkdir(parents=True, exist_ok=True)
    for sub in ("normal", "swap"):
        (cand / sub).mkdir(exist_ok=True)
    ask, writer = writer_ask(a.lane)
    prior = [json.loads(l) for f in sorted(Path(a.out).parent.glob("evolve-*.jsonl")) for l in f.read_text().splitlines()]
    seed = best_or_closest(prior, ref)     # earlier runs scored on the same split; their scores carry over as written
    if seed:
        print(f"seeded from round {seed['round']} of an earlier run: {_fmt(seed['metrics'])}", flush=True)
    score = both_ways(scorer(val, answers, cand / "normal"), scorer(work / "val-swap", work / "answers-swap", cand / "swap"))
    rows = evolve(a.rounds, ask, score, ref, writer, seed)
    top = best(rows, ref)
    stamp = datetime.now(timezone.utc).isoformat(timespec="seconds")
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    with open(a.out, "w") as fh:
        for r in rows:
            fh.write(json.dumps({"at": stamp, "task": REPO, "dataset": DATASET, "split": "validation: site 1 held out",
                                 "reference": {METHOD: ref}, **r}) + "\n")
    print(f"evolve: {len(rows)} rounds by {writer}, {sum('metrics' in r for r in rows)} ran, "
          + (f"best {_fmt(top['metrics'])} (round {top['round']})" if top else "none passes the bar's checks on validation")
          + f"; reference {_fmt(ref)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
