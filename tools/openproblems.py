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
import argparse, base64, json, os, re, subprocess, sys, time, urllib.request
from datetime import datetime, timezone
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]     # run with -I, which leaves the script's own folder off the path

REPO = "openproblems-bio/task_predict_modality"
S3 = "https://openproblems-data.s3.amazonaws.com/resources/task_predict_modality"
RESULTS = "run_2026-10-10_07-15-14"
DATASET = "openproblems_neurips2021/bmmc_cite/normal"
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
    subprocess.run(["docker", "run", "--rm", "-v", f"{d.resolve()}:/data", R_IMAGE, "bash", "-c",
                    f'Rscript -e "install.packages(c({cran}), repos=\\"https://cloud.r-project.org\\", quiet=TRUE)" '
                    f'>/dev/null 2>&1; Rscript /data/metric.R'], check=True, capture_output=True, text=True)
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


BRIEF = """Write a Python function that predicts surface protein levels (ADT, 134 proteins) of single cells from
their RNA expression (13,953 genes), for the openproblems.bio task predict_modality (bmmc_cite, NeurIPS 2021).
Both are normalized (log CP10k for RNA). Cells come from donors at several sites; the test cells are mostly from
a site that training never sees, so batch effects between sites matter.

    def predict(X_train, Y_train, X_test, batch_train, batch_test):
        # X_train: scipy.sparse.csr_matrix (n_train x 13953) RNA;  Y_train: numpy (n_train x 134) protein
        # X_test: scipy.sparse.csr_matrix (n_test x 13953);  batch_*: numpy arrays of donor ids like "s2d4"
        # return numpy (n_test x 134) predicted protein

Scored by rmse over every value (lower is better) and the mean Pearson correlation per cell (higher is better).
Machine: 4 CPU cores, 16 GB RAM, no GPU, 20 minutes for the whole call. Libraries: numpy, scipy, scikit-learn
only, no internet. The reference to beat is k-nearest-neighbor regression on a 50-component TruncatedSVD of the
RNA (train and test together), 100 neighbors, which scores {ref} here.
Reply with the whole function and its imports in one ```python block."""


def extract_code(text):
    """The last ```python block that defines predict()."""
    blocks = [b for b in re.findall(r"```python\n(.*?)```", text or "", re.S) if "def predict(" in b]
    return blocks[-1] if blocks else None


def candidate_cmd(code_file, val_dir, out, user, python):
    """The command that runs one candidate on the validation arrays: as the sandbox user with an empty
    environment when there is one (tools/judge_sandbox.sh), so no secret of this job is in reach."""
    cmd = [python, "-I", str(Path(__file__).resolve()), "run-candidate", code_file, val_dir, out]
    return ["sudo", "-n", "-u", user, "env", "-i", "PATH=/usr/bin:/bin", f"HOME=/tmp/{user}",
            "prlimit", f"--as={CAND_MEM}", "timeout", str(CAND_S), *cmd] if user else cmd


def best(rows, ref):
    """The lowest validation rmse among candidates at least as good as the reference on Pearson per cell."""
    ok = [r for r in rows if "metrics" in r and r["metrics"]["mean_pearson_per_cell"] >= ref["mean_pearson_per_cell"]]
    return min(ok, key=lambda r: r["metrics"]["rmse"]) if ok else None


def _fmt(m):
    return f"rmse {m['rmse']:.4f}, mean Pearson per cell {m['mean_pearson_per_cell']:.4f}"


def evolve(rounds, ask, score, ref, writer):
    """`rounds` asks; each sees the best candidate so far with its validation scores and the last outcome.
    score(code) -> metrics, or {"error": why}. Every attempt is a row."""
    rows = []
    for i in range(rounds):
        prompt = BRIEF.format(ref=_fmt(ref))
        ran = [r for r in rows if "metrics" in r]
        top = best(rows, ref) or (min(ran, key=lambda r: r["metrics"]["rmse"]) if ran else None)
        if top:          # the closest so far, shown even below the reference's Pearson (run 39519234354: 3 ran, none at it)
            prompt += (f"\n\nThe strongest so far scores {_fmt(top['metrics'])}; beat the reference on both:"
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
        row = {"round": i, "writer": writer, "ask_s": round(time.time() - t, 1)}
        code = extract_code(reply) if isinstance(reply, str) else None
        if code is None:
            row["error"] = "no code in the reply" if isinstance(reply, str) else f"no reply: {reply.get('error')}"
        else:
            r = score(code)
            row.update(code=code, **({"error": r["error"]} if "error" in r else {"metrics": r}))
        rows.append(row)
        print(json.dumps({k: v for k, v in row.items() if k != "code"})[:400], flush=True)
    return rows


def fetch_script(path, sha):
    raw = subprocess.run(["gh", "api", f"repos/{REPO}/contents/{path}?ref={sha}", "-q", ".content"],
                         capture_output=True, text=True, check=True).stdout
    return base64.b64decode(raw).decode()


def run_script(src, name, par, meta):
    t = time.time()
    exec(compile(with_par(src, par, meta), name, "exec"), {"__name__": "__main__"})
    return round(time.time() - t, 1)


def prepare(data, val, answers):
    """Validation arrays (all of site 1 held out) where the sandbox can read them, the answers where it cannot,
    and the reference's validation scores from the task's own knnr_py script."""
    import anndata as ad
    from scipy import sparse
    m1, m2 = ad.read_h5ad(data / "train_mod1.h5ad"), ad.read_h5ad(data / "train_mod2.h5ad")
    v = held_out(m1.obs["batch"].astype(str).values)
    val.mkdir(parents=True, exist_ok=True)
    answers.mkdir(parents=True, exist_ok=True)
    dense = lambda a: a.toarray() if sparse.issparse(a) else np.asarray(a)
    sparse.save_npz(val / "X_train.npz", sparse.csr_matrix(m1.layers["normalized"][~v]))
    np.save(val / "Y_train.npy", dense(m2.layers["normalized"][~v]).astype(np.float32))
    sparse.save_npz(val / "X_test.npz", sparse.csr_matrix(m1.layers["normalized"][v]))
    np.save(val / "batch_train.npy", m1.obs["batch"].astype(str).values[~v])
    np.save(val / "batch_test.npy", m1.obs["batch"].astype(str).values[v])
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
    ref = metrics(y_val, dense(ad.read_h5ad(h5 / "ref.h5ad").layers["normalized"]))
    (answers / "ref.json").write_text(json.dumps(ref))
    return ref


def run_candidate(code_file, val, out):
    """Inside the sandbox: one candidate's predict() on the validation inputs, its output saved as plain floats."""
    from scipy import sparse
    ns = {"__name__": "candidate"}
    exec(compile(Path(code_file).read_text(), "candidate.py", "exec"), ns)
    val = Path(val)
    y = ns["predict"](sparse.load_npz(val / "X_train.npz"), np.load(val / "Y_train.npy"), sparse.load_npz(val / "X_test.npz"),
                      np.load(val / "batch_train.npy", allow_pickle=True), np.load(val / "batch_test.npy", allow_pickle=True))
    np.save(out, np.asarray(y, dtype=np.float32))


def scorer(val, answers, work, user, python):
    y_val = np.load(answers / "Y_val.npy")
    n = [0]

    def score(code):
        n[0] += 1
        code_file, out = work / f"cand{n[0]}.py", work / f"cand{n[0]}.npy"
        code_file.write_text(code)
        try:
            r = subprocess.run(candidate_cmd(str(code_file), str(val), str(out), user, python), capture_output=True,
                               text=True, timeout=CAND_S + 60)
        except subprocess.TimeoutExpired:
            return {"error": f"over {CAND_S} s"}
        if r.returncode != 0 or not out.exists():
            return {"error": f"exit {r.returncode}: {(r.stderr or r.stdout)[-1500:]}"}
        p = np.load(out, allow_pickle=False)
        if p.shape != y_val.shape or not np.isfinite(p).all():
            return {"error": f"prediction shape {p.shape} (want {y_val.shape}) or non-finite values"}
        return {k: round(v, 4) for k, v in metrics(y_val, p).items()}
    return score


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


def download(data):
    data.mkdir(parents=True, exist_ok=True)
    for f in FILES:
        if not (data / f"{f}.h5ad").exists():
            urllib.request.urlretrieve(f"{S3}/datasets/{DATASET}/{NORM}/{f}.h5ad", data / f"{f}.h5ad")


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


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["reproduce", "prepare", "evolve", "run-candidate"])
    ap.add_argument("args", nargs="*", help="run-candidate: CODE VAL_DIR OUT (inside the sandbox)")
    ap.add_argument("--work", help="scratch: data/, val/ (sandbox-readable), answers/ (not), candidates/")
    ap.add_argument("--out", help="the ledger file to write")
    ap.add_argument("--rounds", type=int, default=12)
    ap.add_argument("--lane", default="leanstral")
    a = ap.parse_args()
    if a.cmd == "run-candidate":
        run_candidate(*a.args)
        return 0
    work = Path(a.work)
    if a.cmd == "reproduce":
        return reproduce(work, a.out)
    val, answers = work / "val", work / "answers"
    if a.cmd == "prepare":
        download(work / "data")
        print(json.dumps({"reference_on_validation": prepare(work / "data", val, answers)}))
        return 0
    ref = json.loads((answers / "ref.json").read_text())
    cand = work / "candidates"
    cand.mkdir(parents=True, exist_ok=True)
    ask, writer = writer_ask(a.lane)
    rows = evolve(a.rounds, ask, scorer(val, answers, cand, os.environ.get("SB_JUDGE_USER"), sys.executable), ref, writer)
    top = best(rows, ref)
    stamp = datetime.now(timezone.utc).isoformat(timespec="seconds")
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    with open(a.out, "w") as fh:
        for r in rows:
            fh.write(json.dumps({"at": stamp, "task": REPO, "dataset": DATASET, "split": "validation: site 1 held out",
                                 "reference": {METHOD: ref}, **r}) + "\n")
    print(f"evolve: {len(rows)} rounds by {writer}, {sum('metrics' in r for r in rows)} ran, "
          + (f"best {_fmt(top['metrics'])} (round {top['round']})" if top else "none at the reference's Pearson")
          + f"; reference {_fmt(ref)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
