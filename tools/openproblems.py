"""Reproduce one openproblems.bio leaderboard entry on our own machine (task #477, DECISIONS.md 2026-10-20): the
task's own method and metric scripts, fetched at a pinned commit and run unchanged except for their VIASH
parameter block, on the task's public data, scored against the maintainers' own results file. The gate is every
compared metric within 1%; a run that compares nothing never passes.

    python3 tools/openproblems.py --work /tmp/op --out ledger/openproblems/RUN.json

Needs anndata, scikit-learn and pyyaml. R metrics (correlation) are not run yet; the row says which were compared.
"""
import argparse, base64, json, re, subprocess, sys, time, urllib.request
from datetime import datetime, timezone
from pathlib import Path

REPO = "openproblems-bio/task_predict_modality"
S3 = "https://openproblems-data.s3.amazonaws.com/resources/task_predict_modality"
RESULTS = "run_2026-10-10_07-15-14"
DATASET = "openproblems_neurips2021/bmmc_cite/normal"
NORM = "log_cp10k"                           # knnr_py's preferred_normalization (its config.vsh.yaml)
METHOD, PARAMS = "knnr_py", {"distance_method": "minkowski", "n_pcs": 50, "n_neighbors": 100}   # config defaults
METRICS = ("mse",)
TOLERANCE_PCT = 1.0
FILES = ("train_mod1", "train_mod2", "test_mod1", "test_mod2")


def with_par(src, par, meta):
    """The script with its VIASH block replaced by our parameters; nothing else changes."""
    return re.sub(r"## VIASH START\n.*?## VIASH END\n", lambda _: f"par = {par!r}\nmeta = {meta!r}\n", src, flags=re.S)


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


def fetch_script(path, sha):
    raw = subprocess.run(["gh", "api", f"repos/{REPO}/contents/{path}?ref={sha}", "-q", ".content"],
                         capture_output=True, text=True, check=True).stdout
    return base64.b64decode(raw).decode()


def run_script(src, name, par, meta):
    t = time.time()
    exec(compile(with_par(src, par, meta), name, "exec"), {"__name__": "__main__"})
    return round(time.time() - t, 1)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--work", required=True, help="a scratch directory for the data and outputs")
    ap.add_argument("--out", help="the ledger row to write")
    a = ap.parse_args()
    import anndata as ad, yaml
    work = Path(a.work)
    data = work / "data"
    data.mkdir(parents=True, exist_ok=True)
    sha = subprocess.run(["gh", "api", f"repos/{REPO}/commits/main", "-q", ".sha"], capture_output=True, text=True,
                         check=True).stdout.strip()
    for f in FILES:
        if not (data / f"{f}.h5ad").exists():
            urllib.request.urlretrieve(f"{S3}/datasets/{DATASET}/{NORM}/{f}.h5ad", data / f"{f}.h5ad")
    pred = str(work / "prediction.h5ad")
    seconds = {METHOD: run_script(fetch_script(f"src/methods/{METHOD}/script.py", sha), METHOD,
                                  {"input_train_mod1": str(data / "train_mod1.h5ad"),
                                   "input_train_mod2": str(data / "train_mod2.h5ad"),
                                   "input_test_mod1": str(data / "test_mod1.h5ad"), "output": pred, **PARAMS},
                                  {"name": METHOD})}
    got = {}
    for m in METRICS:
        out = str(work / f"score_{m}.h5ad")
        seconds[m] = run_script(fetch_script(f"src/metrics/{m}/script.py", sha), m,
                                {"input_test_mod2": str(data / "test_mod2.h5ad"), "input_prediction": pred, "output": out},
                                {"name": m})
        u = ad.read_h5ad(out).uns
        got.update(zip(u["metric_ids"], map(float, u["metric_values"])))
    with urllib.request.urlopen(f"{S3}/results/{RESULTS}/score_uns.yaml") as r:
        pub = published(yaml.safe_load(r.read()), DATASET, METHOD)
    row = {"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "task": REPO, "commit": sha,
           "results": RESULTS, "dataset": DATASET, "normalization": NORM, "method": METHOD, "params": PARAMS,
           "metrics_run": list(METRICS), "tolerance_pct": TOLERANCE_PCT, "seconds": seconds, **compare(got, pub)}
    print(json.dumps(row, indent=1))
    if a.out:
        Path(a.out).parent.mkdir(parents=True, exist_ok=True)
        Path(a.out).write_text(json.dumps(row) + "\n")
    return 0 if row["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
