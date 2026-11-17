"""The rebuild's own logic (kumori #477): which cells are training cells, and when a rebuild counts as the same
benchmark. The heavy path (GEO, upstream's scripts, knnr_py) runs only in openproblems_rebuild.yml."""
import json, tempfile, unittest
from unittest import mock
from pathlib import Path

import numpy as np
from scipy import sparse

import openproblems_rebuild as rb

FP = "e88684e2b6297fd11e9045d45f087680592b355908278e366ae4b0c48d66c430"


class TrainRows(unittest.TestCase):
    def test_train_cells_with_counts_in_both_modalities_in_file_order(self):
        c1 = sparse.csc_matrix(np.array([[1, 0], [0, 0], [2, 1], [0, 3], [1, 1]], dtype=np.float32))
        c2 = sparse.csc_matrix(np.array([[1], [5], [0], [2], [4]], dtype=np.float32))
        is_train = np.array(["train", "train", "train", "test", "train"])
        # row 1 has no counts in the first modality, row 2 none in the second, row 3 is a test cell
        self.assertEqual(rb.train_rows(c1, c2, is_train).tolist(), [0, 4])

    def test_the_swap_direction_takes_the_same_cells(self):
        c1 = sparse.csr_matrix(np.array([[1, 0], [0, 0], [2, 1]], dtype=np.float32))
        c2 = sparse.csr_matrix(np.array([[1], [5], [3]], dtype=np.float32))
        t = np.array(["train"] * 3)
        self.assertEqual(rb.train_rows(c1, c2, t).tolist(), rb.train_rows(c2, c1, t).tolist())

    def test_a_categorical_like_label_is_read_as_text(self):
        c = sparse.csc_matrix(np.ones((2, 1), dtype=np.float32))
        self.assertEqual(rb.train_rows(c, c, np.array(["train", "test"], dtype=object)).tolist(), [0])


class Cast(unittest.TestCase):
    def test_float64_changes_the_width_and_not_the_values(self):
        m = sparse.csc_matrix(np.array([[0.1, 0], [0, 2.5]], dtype=np.float32))
        w = rb.cast(m, "float64")
        self.assertEqual((w.dtype, type(w)), (np.float64, type(m)))
        self.assertTrue((w.toarray() == m.toarray().astype(np.float64)).all())
        self.assertIs(rb.cast(m, "as_written"), m)


class Verdict(unittest.TestCase):
    def test_one_matching_variant_is_the_same_benchmark(self):
        self.assertEqual(rb.verdict(FP, {"float64": {"pred_fp": "0" * 64}, "as_written": {"pred_fp": FP}}), "same")

    def test_a_match_decides_at_once_before_the_other_variant_ran(self):
        self.assertEqual(rb.verdict(FP, {"float64": {"pred_fp": FP}}), "same")

    def test_no_match_among_every_planned_variant_is_not_reproduced(self):
        self.assertEqual(rb.verdict(FP, {"float64": {"pred_fp": "0" * 64}, "as_written": {"pred_fp": "1" * 64}}), "not_reproduced")

    def test_a_run_that_died_after_one_miss_decides_nothing(self):
        # Codex 20261117T205540499338Z f1: the receipt is saved after each variant and uploaded even when the run dies
        self.assertEqual(rb.verdict(FP, {"float64": {"pred_fp": "0" * 64}}), "incomplete")

    def test_nothing_measured_decides_nothing(self):
        self.assertEqual(rb.verdict(FP, {}), "incomplete")
        self.assertEqual(rb.verdict(FP, {"float64": {"rmse": 0.97}, "as_written": {"pred_fp": "1" * 64}}), "incomplete")

    def test_close_metrics_without_the_digest_are_not_the_same(self):
        got = {"float64": {"pred_fp": FP[:-1] + "1", "rmse": 0.9691516160964966}, "as_written": {"pred_fp": "1" * 64}}
        self.assertEqual(rb.verdict(FP, got), "not_reproduced")


class Recorded(unittest.TestCase):
    def test_reads_the_reference_from_an_evolve_files_first_row(self):
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "evolve-1.jsonl"
            f.write_text(json.dumps({"reference": {"knnr_py": {"pred_fp": FP, "rmse": 0.96}}}) + "\n" + json.dumps({"round": 1}) + "\n")
            self.assertEqual(rb.recorded(f)["pred_fp"], FP)

    def test_the_ledgers_last_good_run_carries_the_digest_the_rule_names(self):
        f = Path(__file__).resolve().parent.parent / "ledger" / "openproblems" / "evolve-41869521760.jsonl"
        self.assertEqual(rb.recorded(f)["pred_fp"], FP)


class Ensure(unittest.TestCase):
    """openproblems.download's builder: both directions cut from one build, the as-written variant, the cell count held."""
    def run_ensure(self, d, swap, n=rb.TRAIN_CELLS, fp="recorded"):
        calls = {"source": 0, "written": []}
        work = Path(d) / "rebuild"
        def source(w):
            calls["source"] += 1
            for m in ("mod1.zarr", "mod2.zarr"):
                (w / m).mkdir(parents=True)
        rb.ensure(Path(d) / ("data-swap" if swap else "data"), swap=swap, source=source, fingerprint=lambda *a: fp,
                  modalities=lambda w: ("GEX", "ADT", list(range(n))),
                  write=lambda a1, a2, rows, out, variant: calls["written"].append((a1, a2, len(rows), out.name, variant)))
        return calls

    def test_normal_is_gex_in_protein_out_and_swap_the_other_way_round(self):
        with tempfile.TemporaryDirectory() as d:
            a = self.run_ensure(d, swap=False)
            b = self.run_ensure(d, swap=True)
        self.assertEqual(a["written"], [("GEX", "ADT", rb.TRAIN_CELLS, "data", "as_written")])
        self.assertEqual(b["written"], [("ADT", "GEX", rb.TRAIN_CELLS, "data-swap", "as_written")])
        self.assertEqual((a["source"], b["source"]), (1, 0))       # the second direction reuses the first's build

    def setUp(self):
        self._fp = dict(rb.op.DATA_LAYERS_FP)
        rb.op.DATA_LAYERS_FP[rb.op.DATA_VERSION] = "recorded"

    def tearDown(self):
        rb.op.DATA_LAYERS_FP.update(self._fp)

    def test_layers_with_another_digest_write_nothing(self):
        with tempfile.TemporaryDirectory() as d, self.assertRaises(SystemExit) as e:
            self.run_ensure(d, swap=False, fp="drifted")
        self.assertIn("nothing written", str(e.exception))

    def test_no_recorded_digest_refuses_every_build(self):
        rb.op.DATA_LAYERS_FP[rb.op.DATA_VERSION] = None
        with tempfile.TemporaryDirectory() as d, self.assertRaises(SystemExit):
            self.run_ensure(d, swap=False, fp="anything")

    def test_a_rebuild_with_another_cell_count_writes_nothing(self):
        with tempfile.TemporaryDirectory() as d, self.assertRaises(SystemExit) as e:
            self.run_ensure(d, swap=False, n=rb.TRAIN_CELLS - 1)
        self.assertIn("nothing written", str(e.exception))


class LayersFp(unittest.TestCase):
    class A:
        def __init__(self, m): self.layers = {"normalized": m}

    def fp(self, g, a, rows=(0, 1)):
        return rb.layers_fp(self.A(g), self.A(a), list(rows))

    def test_names_the_numbers_not_the_storage(self):
        g = np.array([[0.5, 0, 2], [0, 1.5, 0], [9, 9, 9]], dtype=np.float32)
        a = np.array([[1.0], [0], [3]], dtype=np.float32)
        base = self.fp(sparse.csr_matrix(g), sparse.csc_matrix(a))
        self.assertEqual(base, self.fp(sparse.csc_matrix(g), sparse.csr_matrix(a)))
        self.assertEqual(base, self.fp(sparse.csr_matrix(g.astype(np.float64)), sparse.csc_matrix(a)))
        g2 = g.copy(); g2[1, 1] = np.nextafter(np.float32(1.5), np.float32(2))
        self.assertNotEqual(base, self.fp(sparse.csr_matrix(g2), sparse.csc_matrix(a)))        # one bit in one value
        self.assertNotEqual(base, self.fp(sparse.csr_matrix(g), sparse.csc_matrix(a), rows=(1, 0)))   # cell order
        self.assertNotEqual(base, self.fp(sparse.csr_matrix(g), sparse.csc_matrix(a), rows=(0, 2)))   # which cells


class DataVersion(unittest.TestCase):
    """openproblems.py's side (DECISIONS 2026-11-17): what a step may read on this data version, and under what name."""
    op = rb.op

    def test_training_files_are_built_when_missing_and_left_alone_when_there(self):
        with tempfile.TemporaryDirectory() as d:
            data, built = Path(d) / "data", []
            build = lambda dd, swap: built.append((dd.name, swap))
            self.op.download(data, files=self.op.TRAIN_FILES, build=build)
            self.op.download(data, self.op.SWAP, files=self.op.TRAIN_FILES, build=build)
            self.assertEqual(built, [("data", False), ("data", True)])
            data.mkdir()
            for f in self.op.TRAIN_FILES:
                (data / f"{f}.h5ad").write_text("x")
            self.op.download(data, files=self.op.TRAIN_FILES, build=build)
            self.assertEqual(len(built), 2)

    def test_a_step_that_needs_the_test_files_is_closed_and_builds_nothing(self):
        with tempfile.TemporaryDirectory() as d:
            built = []
            for files in (self.op.FILES, ("test_mod2",)):
                with self.assertRaises(self.op.Closed):
                    self.op.download(Path(d) / "data", files=files, build=lambda *a, **k: built.append(1))
            self.assertEqual(built, [])

    def test_a_reference_with_another_digest_scores_nothing(self):
        self.op.check_data_version({"pred_fp": self.op.DATA_REF_FP[self.op.DATA_VERSION]})
        for ref in ({"pred_fp": FP}, {"pred_fp": None}, {}):       # the S3 era's digest is refused like any other
            with self.assertRaises(SystemExit):
                self.op.check_data_version(ref)

    def test_the_scheduled_qualify_picks_only_this_versions_rows(self):
        ref = {"rmse": 1.0, "mae": 1.0, "mean_pearson_per_cell": 0.5}
        row = lambda v: {"round": 1, "code": "def predict(*a): return 1", "reference": {"knnr_py": ref},
                         "metrics": {"rmse": 0.9, "mae": 0.9, "mean_pearson_per_cell": 0.6}, **({"data_version": v} if v else {})}
        with mock.patch.object(self.op, "passes_bar", lambda r, ref: True):
            self.assertIsNone(self.op.next_qualify({"evolve-old.jsonl": [row(None)]}, []))
            self.assertIsNone(self.op.next_qualify({"evolve-x.jsonl": [row("some-other-version")]}, []))
            self.assertEqual(self.op.next_qualify({"evolve-old.jsonl": [row(None)], "evolve-new.jsonl": [row(self.op.DATA_VERSION)]}, []),
                             {"evolve_file": "evolve-new.jsonl", "round": 1})

    def test_rows_and_receipts_without_the_field_are_the_s3_era(self):
        self.assertEqual(self.op.row_version({}), "s3-2026-10")
        self.assertEqual(self.op.row_version({"data_version": "geo-rebuild-1"}), "geo-rebuild-1")

    def test_an_s3_era_row_is_never_this_versions_row(self):
        # same_reference is the gate every seed and prior row passes: metrics inside the tolerance are not enough
        ref = {"rmse": 0.9691365957260132, "mae": 0.6671521663665771, "mean_pearson_per_cell": 0.7856988555775423,
               "bootstrap": True, "pred_fp": self.op.DATA_REF_FP["geo-rebuild-1"],
               "swap": {"rmse": 0.3229, "mae": 0.1554, "mean_pearson_per_cell": 0.5}}
        old = {"reference": {"knnr_py": {**ref, "rmse": 0.9691516160964966, "pred_fp": FP}}}
        self.assertFalse(self.op.same_reference(old, ref))
        self.assertTrue(self.op.same_reference({"reference": {"knnr_py": dict(ref)}}, ref))


if __name__ == "__main__":
    unittest.main()
