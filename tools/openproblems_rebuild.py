#!/usr/bin/env python3
"""Rebuild predict_modality's bmmc_cite training files from the public GEO deposit, and say whether the rebuild is
the benchmark we measured on (kumori #477; DECISIONS 2026-11-05 checkpoint, Codex 20261105T172845378225Z).

Why: openproblems-data.s3.amazonaws.com has answered 403 AllAccessDisabled for every object since 2026-11-05, the
maintainers have not answered task_predict_modality#85, and no copy of the processed split was kept. The rule set
on 11-05: a rebuild is the same benchmark only if knnr_py's validation prediction has the recorded digest
(pred_fp, sha256 of the float32 array), byte for byte; otherwise it is a separately versioned benchmark.

What runs, in order:
  1. GSE194122's processed CITE-seq h5ad.gz from NCBI's FTP (the input upstream's own resource script names),
     its sha256 recorded.
  2. Upstream's scripts, unchanged except for their VIASH block (openproblems.with_par): the datasets repo's
     loader, log_cp (10,000 counts per cell) on GEX and prot_clr on ADT, at DATASETS_SHA.
  3. The training half of the task's process_dataset/script.R, ported here because it draws nothing at random:
     cells with counts in both modalities, obs['is_train'] == 'train', in the file's order. The test half samples
     1,000 cells with R's generator and is not rebuilt here; the reference digest needs only the training files.
  4. openproblems.prepare on the result: the task's own knnr_py on the site-1 validation split, its pred_fp
     beside the recorded one.

R has no 32-bit float, so the files upstream's R step wrote most likely hold 64-bit values; the loader's are 32-bit.
Both are tried (VARIANTS) and each digest is reported: a sha256 cannot match by chance, so a match by either is
the proof, and the receipt names which.
"""
import argparse, gzip, hashlib, json, shutil, subprocess, sys, base64, urllib.request
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import openproblems as op

GEO = ("https://ftp.ncbi.nlm.nih.gov/geo/series/GSE194nnn/GSE194122/suppl/"
       "GSE194122%5Fopenproblems%5Fneurips2021%5Fcite%5FBMMC%5Fprocessed%2Eh5ad%2Egz")
DATASETS_REPO = "openproblems-bio/datasets"
DATASETS_SHA = "ee5575cb14089f632c4acb54456152259e0f118f"      # datasets main, read 2026-11-17
LOADER = "src/loaders/multimodal/openproblems_neurips2021_bmmc/script.py"
LOG_CP = "src/normalization/log_cp/script.py"
PROT_CLR = "src/normalization/prot_clr/script.py"
DATASET_ID = "openproblems_neurips2021/bmmc_cite"
TRAIN_CELLS = 66175      # 51,506 kept + 14,669 held out at site 1 (openproblems.py's swap notes, measured on the S3 files)
VARIANTS = ("float64", "as_written")


def fetch(repo, path, sha):
    raw = subprocess.run(["gh", "api", f"repos/{repo}/contents/{path}?ref={sha}", "-q", ".content"],
                         capture_output=True, text=True, check=True).stdout
    return base64.b64decode(raw).decode()


def download(url, gz, out):
    """The deposit, streamed to disk and unpacked; returns the sha256 of the .gz as served."""
    h = hashlib.sha256()
    with urllib.request.urlopen(url, timeout=120) as r, open(gz, "wb") as f:
        while chunk := r.read(1 << 20):
            h.update(chunk)
            f.write(chunk)
    with gzip.open(gz, "rb") as src, open(out, "wb") as dst:
        shutil.copyfileobj(src, dst, 1 << 20)
    return h.hexdigest()


def train_rows(counts1, counts2, is_train):
    """process_dataset/script.R's training cells, as row numbers in file order: cells with counts in both
    modalities, then those marked 'train'. No random draw is involved."""
    keep = (np.asarray(counts1.sum(axis=1)).ravel() > 0) & (np.asarray(counts2.sum(axis=1)).ravel() > 0)
    return np.flatnonzero(keep & (np.asarray(is_train).astype(str) == "train"))


def cast(layer, variant):
    return layer.astype(np.float64) if variant == "float64" else layer


def write_train(ad1, ad2, rows, out, variant):
    """train_mod1/train_mod2 as script.R lays them out: counts and normalized layers, obs batch (and size_factors
    where the modality has them) from the first modality, the var columns it keeps, the uns it carries."""
    import anndata as ad
    out.mkdir(parents=True, exist_ok=True)
    obs = ad1.obs.iloc[rows][[c for c in ("batch", "size_factors") if c in ad1.obs.columns]]
    for name, a in (("train_mod1", ad1), ("train_mod2", ad2)):
        ad.AnnData(layers={k: cast(a.layers[k][rows], variant) for k in ("counts", "normalized")}, obs=obs.copy(),
                   var=a.var[[c for c in ("gene_ids", "hvg", "hvg_score") if c in a.var.columns]].copy(),
                   uns={"dataset_id": DATASET_ID, "normalization_id": str(a.uns.get("normalization_id"))}
                   ).write_h5ad(out / f"{name}.h5ad")


def layers_fp(gex, adt, rows):
    """sha256 of the two normalized training layers, in one canonical form (CSR, sorted, no duplicates, 32-bit
    little-endian values), so it names the numbers and not how a library happened to store them."""
    from scipy import sparse
    h = hashlib.sha256()
    for layer in (gex.layers["normalized"], adt.layers["normalized"]):
        m = sparse.csr_matrix(layer[rows])
        m.sum_duplicates()
        m.sort_indices()
        h.update(repr(m.shape).encode())
        for part, kind in ((m.indptr, "<i8"), (m.indices, "<i8"), (m.data, "<f4")):
            h.update(np.ascontiguousarray(part.astype(kind)).tobytes())
    return h.hexdigest()


def recorded(evolve_file):
    """The reference as the ledger last recorded it on the S3 files: the first row of an evolve file."""
    return json.loads(Path(evolve_file).read_text().splitlines()[0])["reference"]["knnr_py"]


def versions():
    out = {}
    for m in ("numpy", "scipy", "sklearn", "anndata", "scanpy", "muon", "pandas", "h5py", "zarr"):
        try:
            out[m] = __import__(m).__version__
        except Exception as e:
            out[m] = f"missing: {type(e).__name__}"
    return out


def verdict(expected_fp, got, planned=VARIANTS):
    """same: a variant's digest is the recorded one (one match is enough, at once). not_reproduced: every planned
    variant produced a digest and none is the recorded one; that says this reconstruction, with these library
    versions on this machine, did not reproduce the reference's prediction, not that the GEO deposit differs from
    the S3 split (Codex 20261117T205540499338Z f1, f2). Anything else, a run that died part-way included, is
    incomplete and decides nothing."""
    if any(v.get("pred_fp") == expected_fp for v in got.values()):
        return "same"
    if all(got.get(v, {}).get("pred_fp") for v in planned):
        return "not_reproduced"
    return "incomplete"


def source(work, receipt=None):
    """GEO to the two normalized modalities (work/mod1.zarr GEX, work/mod2.zarr ADT) through upstream's own scripts."""
    work.mkdir(parents=True, exist_ok=True)
    sha = download(GEO, work / "geo.h5ad.gz", work / "geo.h5ad")
    if receipt is not None:
        receipt["source_sha256"] = sha
    (work / "geo.h5ad.gz").unlink()
    meta = lambda n: {"name": n, "resources_dir": str(work)}
    op.run_script(fetch(DATASETS_REPO, LOADER, DATASETS_SHA), "loader",
                  {"input": str(work / "geo.h5ad"), "mod1": "GEX", "mod2": "ADT", "dataset_id": DATASET_ID,
                   "output_mod1": str(work / "raw_mod1.zarr"), "output_mod2": str(work / "raw_mod2.zarr")},
                  meta("openproblems_neurips2021_bmmc"))
    (work / "geo.h5ad").unlink()
    op.run_script(fetch(DATASETS_REPO, LOG_CP, DATASETS_SHA), "log_cp",
                  {"input": str(work / "raw_mod1.zarr"), "output": str(work / "mod1.zarr"), "n_cp": 10000,
                   "layer_output": "normalized", "obs_size_factors": "size_factors", "normalization_id": "log_cp10k"},
                  meta("log_cp10k"))
    op.run_script(fetch(DATASETS_REPO, PROT_CLR, DATASETS_SHA), "prot_clr",
                  {"input": str(work / "raw_mod2.zarr"), "output": str(work / "mod2.zarr"),
                   "layer_output": "normalized", "normalization_id": "prot_clr"}, meta("prot_clr"))


def modalities(work):
    import anndata as ad
    gex, adt = ad.read_zarr(work / "mod1.zarr"), ad.read_zarr(work / "mod2.zarr")
    return gex, adt, train_rows(gex.layers["counts"], adt.layers["counts"], gex.obs["is_train"])


def ensure(data, swap=False, source=source, modalities=modalities, write=write_train, fingerprint=layers_fp):
    """One direction's training files in `data`, for openproblems.download: data version geo-rebuild-1 is the
    as-written (32-bit) variant. The two modalities are built once, beside the first folder asked for, and both
    directions are cut from them."""
    work = Path(data).parent / "rebuild"
    if not ((work / "mod1.zarr").exists() and (work / "mod2.zarr").exists()):
        source(work)
    gex, adt, rows = modalities(work)
    if len(rows) != TRAIN_CELLS:
        sys.exit(f"the rebuild has {len(rows)} training cells, not the {TRAIN_CELLS} of data version geo-rebuild-1; nothing written")
    want, got = op.DATA_LAYERS_FP[op.DATA_VERSION], fingerprint(gex, adt, rows)
    if got != want:
        sys.exit(f"the rebuilt training layers' digest is {got[:12]}, not the {str(want)[:12]} recorded for data version "
                 f"{op.DATA_VERSION}; nothing written")
    write(*((adt, gex) if swap else (gex, adt)), rows, Path(data), "as_written")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", required=True)
    ap.add_argument("--expect-from", required=True, help="an evolve-<run>.jsonl whose first row holds the reference")
    ap.add_argument("--out", required=True, help="the receipt (JSON)")
    a = ap.parse_args()
    work = Path(a.work)
    work.mkdir(parents=True, exist_ok=True)
    want = recorded(a.expect_from)
    receipt = {"source": GEO, "datasets_sha": DATASETS_SHA, "upstream": op.UPSTREAM_SHA, "expected": want,
               "versions": versions(), "variants": {}}

    def save():
        receipt["verdict"] = verdict(want["pred_fp"], receipt["variants"])
        Path(a.out).write_text(json.dumps(receipt, indent=1) + "\n")

    save()                                               # a run that dies still leaves what it knew
    source(work, receipt)
    gex, adt, rows = modalities(work)
    receipt["shape"] = {"cells": int(gex.n_obs), "train_cells": int(len(rows)), "genes": int(gex.n_vars),
                        "proteins": int(adt.n_vars), "train_cells_expected": TRAIN_CELLS,
                        "layer_dtype": {"gex": str(gex.layers["normalized"].dtype), "adt": str(adt.layers["normalized"].dtype)},
                        "layer_format": {"gex": type(gex.layers["normalized"]).__name__, "adt": type(adt.layers["normalized"]).__name__}}
    receipt["layers_fp"] = layers_fp(gex, adt, rows)
    save()
    print(json.dumps(receipt["shape"]), flush=True)
    print(f"layers_fp {receipt['layers_fp']}", flush=True)
    for variant in VARIANTS:
        d = work / variant
        write_train(gex, adt, rows, d / "data", variant)
        ref = op.prepare(d / "data", d / "val", d / "answers")
        receipt["variants"][variant] = {**ref, "same_digest": ref["pred_fp"] == want["pred_fp"],
                                        "is_geo_rebuild_1": ref["pred_fp"] == op.DATA_REF_FP["geo-rebuild-1"]}
        save()
        print(f"{variant}: pred_fp {ref['pred_fp'][:12]} (recorded on S3 {want['pred_fp'][:12]}, geo-rebuild-1 "
              f"{op.DATA_REF_FP['geo-rebuild-1'][:12]}), rmse {ref['rmse']:.6f} (recorded {want['rmse']:.6f}), Pearson "
              f"{ref['mean_pearson_per_cell']:.6f} (recorded {want['mean_pearson_per_cell']:.6f})", flush=True)
        if ref["pred_fp"] == want["pred_fp"]:           # the swap direction on the variant that is the benchmark
            write_train(adt, gex, rows, d / "data-swap", variant)
            receipt["variants"][variant]["swap"] = op.prepare_swap(d / "data-swap", d / "val-swap", d / "answers-swap")
            break
        shutil.rmtree(d)                                 # a variant that is not the benchmark: its files go, for disk
    save()
    print(f"verdict: {receipt['verdict']}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
