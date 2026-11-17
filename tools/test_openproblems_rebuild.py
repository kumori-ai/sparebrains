"""The rebuild's own logic (kumori #477): which cells are training cells, and when a rebuild counts as the same
benchmark. The heavy path (GEO, upstream's scripts, knnr_py) runs only in openproblems_rebuild.yml."""
import json, tempfile, unittest
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


if __name__ == "__main__":
    unittest.main()
