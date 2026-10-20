"""tools/openproblems.py: the upstream script runs with only its VIASH block swapped, the published score is read
from the maintainers' own results file, and the 1% gate fails a wrong run (the canary). No network, no data."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import openproblems as op

SCRIPT = "import x\n## VIASH START\npar = {'n_pcs': 4}\nmeta = {'name': 'foo'}\n## VIASH END\nprint(par['n_pcs'])\n"
SCORES = [{"dataset_id": "openproblems_neurips2021/bmmc_cite/normal", "method_id": "knnr_py",
           "metric_ids": ["rmse", "mae"], "metric_values": [0.7233, 0.5255]},
          {"dataset_id": "openproblems_neurips2021/bmmc_cite/normal", "method_id": "knnr_py",
           "metric_ids": ["mean_pearson_per_cell"], "metric_values": [0.7707]},
          {"dataset_id": "openproblems_neurips2021/bmmc_cite/swap", "method_id": "knnr_py",
           "metric_ids": ["rmse", "mae"], "metric_values": [0.3502, 0.1681]}]


class Reproduce(unittest.TestCase):
    def test_only_the_viash_block_changes(self):
        out = op.with_par(SCRIPT, {"n_pcs": 50}, {"name": "knnr_py"})
        self.assertEqual(out, "import x\npar = {'n_pcs': 50}\nmeta = {'name': 'knnr_py'}\nprint(par['n_pcs'])\n")

    def test_the_published_scores_are_one_methods_on_one_dataset(self):
        self.assertEqual(op.published(SCORES, "openproblems_neurips2021/bmmc_cite/normal", "knnr_py"),
                         {"rmse": 0.7233, "mae": 0.5255, "mean_pearson_per_cell": 0.7707})

    def test_within_one_percent_passes_and_the_canary_fails(self):
        pub = {"rmse": 0.7233, "mae": 0.5255}
        ok = op.compare({"rmse": 0.7244, "mae": 0.5264}, pub)
        self.assertTrue(ok["pass"])
        self.assertEqual(ok["metrics"]["rmse"]["diff_pct"], 0.15)
        self.assertFalse(op.compare({"rmse": 0.851, "mae": 0.6126}, pub)["pass"])      # 4 PCs, 5 neighbors
        self.assertFalse(op.compare({}, pub)["pass"], "no metric compared is never a pass")


if __name__ == "__main__":
    unittest.main()
