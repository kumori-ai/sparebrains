"""tools/openproblems.py: the upstream script runs with only its VIASH block swapped, the published score is read
from the maintainers' own results file, and the 1% gate fails a wrong run (the canary). No network, no data."""
import sys
import unittest

import numpy as np
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

    def test_an_r_scripts_viash_block_becomes_an_r_list(self):
        src = 'library(x)\n## VIASH START\npar <- list(\n  output = "o"\n)\n## VIASH END\ncat(par$output)\n'
        self.assertEqual(op.with_par_r(src, {"input_test_mod2": "/data/s.h5ad", "output": "/data/o.h5ad"}),
                         'library(x)\npar <- list(input_test_mod2 = "/data/s.h5ad", output = "/data/o.h5ad")\ncat(par$output)\n')

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


class Validate(unittest.TestCase):
    def test_site_one_is_held_out_like_the_test_sets_site_four(self):
        batches = np.array(["s1d1", "s2d1", "s1d3", "s3d7", "s10d1"])
        self.assertEqual(op.held_out(batches).tolist(), [True, False, True, False, False])

    def test_per_cell_metrics_match_the_task_definitions(self):
        y = np.array([[1.0, 2.0, 3.0], [0.0, 1.0, 0.0]])
        p = np.array([[1.0, 2.0, 4.0], [0.0, 0.0, 1.0]])
        m = op.metrics(y, p)
        self.assertAlmostEqual(m["rmse"], np.sqrt(3 / 6))
        self.assertAlmostEqual(m["mae"], 3 / 6)
        self.assertAlmostEqual(m["mean_pearson_per_cell"], np.mean([np.corrcoef(y[0], p[0])[0, 1], -0.5]))

    def test_the_bootstrap_interval_excludes_zero_only_for_a_real_difference(self):
        rng = np.random.default_rng(0)
        y = rng.normal(size=(400, 20))
        better, worse = y + rng.normal(scale=0.5, size=y.shape), y + rng.normal(scale=1.0, size=y.shape)
        lo, hi = op.paired_bootstrap(y, better, worse, "rmse", n=2000)
        self.assertTrue(hi < 0, "better minus worse rmse is below zero")
        noise = rng.normal(scale=0.7, size=y.shape)
        lo, hi = op.paired_bootstrap(y, y + noise, y - noise, "rmse", n=2000)
        self.assertTrue(lo <= 0 <= hi, "the same error in every cell: the interval holds zero")


GOOD = "```python\nimport numpy as np\n\ndef predict(X_train, Y_train, X_test, batch_train, batch_test):\n    return np.zeros((X_test.shape[0], Y_train.shape[1]))\n```"


class Evolve(unittest.TestCase):
    def test_the_cli_finds_its_sibling_tools_when_run_isolated(self):
        import subprocess
        r = subprocess.run([sys.executable, "-I", str(Path(op.__file__)), "evolve", "--help"], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        r = subprocess.run([sys.executable, "-I", "-c", f"import runpy, sys; sys.argv = ['x']; "
                            f"g = runpy.run_path({str(Path(op.__file__))!r}); import leanstral, decompose"],
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr[-300:])

    def test_the_code_is_the_last_python_block_that_defines_predict(self):
        text = "plan\n```python\nx = 1\n```\nthen\n" + GOOD + "\n```python\nprint('usage')\n```"
        self.assertIn("def predict(", op.extract_code(text))
        self.assertIsNone(op.extract_code("no code here"))

    def test_a_candidate_runs_as_the_sandbox_user_with_an_empty_environment(self):
        cmd = op.candidate_cmd("c.py", "val", "out.npy", user="sbjudge", python="/v/bin/python")
        self.assertEqual(cmd[:6], ["sudo", "-n", "-u", "sbjudge", "env", "-i"])
        self.assertNotIn("KUMORI_API_KEY", " ".join(cmd))
        self.assertEqual(op.candidate_cmd("c.py", "val", "out.npy", user=None, python="py")[:2], ["py", "-I"])

    def test_the_best_is_lowest_rmse_among_those_at_least_as_good_on_pearson(self):
        ref = {"rmse": 0.969, "mean_pearson_per_cell": 0.7855}
        rows = [{"metrics": {"rmse": 0.90, "mean_pearson_per_cell": 0.70}},      # lower rmse, worse Pearson
                {"metrics": {"rmse": 0.95, "mean_pearson_per_cell": 0.79}},
                {"metrics": {"rmse": 0.93, "mean_pearson_per_cell": 0.80}},
                {"error": "Traceback"}]
        self.assertIs(op.best(rows, ref), rows[2])
        self.assertIsNone(op.best([rows[0], rows[3]], ref))

    def test_each_round_shows_the_model_the_best_so_far_and_the_last_outcome(self):
        asked, ref = [], {"rmse": 0.969, "mean_pearson_per_cell": 0.7855}
        replies = iter([GOOD, "no code", GOOD])
        scores = iter([{"rmse": 0.95, "mean_pearson_per_cell": 0.79}, {"rmse": 0.99, "mean_pearson_per_cell": 0.70}])

        def ask(prompt):
            asked.append(prompt)
            return next(replies)
        rows = op.evolve(3, ask, lambda code: next(scores), ref, writer="fake")
        self.assertEqual([("metrics" in r, r.get("error", "")[:7]) for r in rows],
                         [(True, ""), (False, "no code"), (True, "")])
        self.assertIn("0.95", asked[1], "round 2 sees round 1's best")
        self.assertIn("no code", asked[2], "round 3 sees round 2's failure")
        self.assertTrue(all(r["writer"] == "fake" and r["round"] == i for i, r in enumerate(rows)))

    def test_a_run_starts_from_the_best_of_earlier_runs(self):
        asked, ref = [], {"rmse": 0.969, "mean_pearson_per_cell": 0.7855}
        seed = {"round": 7, "code": "def predict(*a):\n    return SEEDED\n", "metrics": {"rmse": 0.9106, "mean_pearson_per_cell": 0.781}}

        def ask(prompt):
            asked.append(prompt)
            return "no code"
        rows = op.evolve(1, ask, lambda code: {}, ref, writer="fake", seed=seed)
        self.assertIn("SEEDED", asked[0])
        self.assertIn("0.9106", asked[0])
        self.assertEqual(len(rows), 1, "the seed is context, not a row of this run")
        prior = [{"metrics": {"rmse": 0.95, "mean_pearson_per_cell": 0.79}, "code": "a"}, seed, {"error": "x"}]
        self.assertIs(op.best_or_closest(prior, ref), prior[0], "at the reference's Pearson beats a lower rmse below it")

    def test_a_crash_comes_back_with_its_code_and_the_closest_is_shown_even_below_the_bar(self):
        asked, ref = [], {"rmse": 0.969, "mean_pearson_per_cell": 0.7855}
        replies = iter([GOOD.replace("np.zeros", "np.ones"), GOOD, GOOD])
        scores = iter([{"error": "ValueError: boom"}, {"rmse": 0.94, "mean_pearson_per_cell": 0.76},
                       {"rmse": 0.96, "mean_pearson_per_cell": 0.75}])

        def ask(prompt):
            asked.append(prompt)
            return next(replies)
        op.evolve(3, ask, lambda code: next(scores), ref, writer="fake")
        self.assertIn("np.ones", asked[1], "the crashed code is shown to be fixed")
        self.assertIn("ValueError: boom", asked[1])
        self.assertIn("0.9400", asked[2], "the closest candidate is shown though its Pearson is below the reference")


if __name__ == "__main__":
    unittest.main()
