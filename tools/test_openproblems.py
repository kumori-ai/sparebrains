"""tools/openproblems.py: the upstream script runs with only its VIASH block swapped, the published score is read
from the maintainers' own results file, and the 1% gate fails a wrong run (the canary). No network, no data."""
import hashlib
import json
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

    def test_params_cover_every_non_path_key_the_reference_reads(self):
        # knnr_py's VIASH keys as of upstream bc9313f98a (2026-11-03), which added `seed` (comp_method.yaml default 0)
        upstream = {"input_train_mod1", "input_train_mod2", "input_test_mod1", "distance_method", "output",
                    "n_pcs", "n_neighbors", "seed"}
        self.assertEqual(upstream - {k for k in upstream if k.startswith(("input_", "output"))}, set(op.PARAMS))
        self.assertEqual(op.PARAMS["seed"], 0)

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

    def test_the_brief_names_the_pitfalls_that_crashed_earlier_candidates(self):
        for hint in ("sklearn.multioutput", "scipy.stats", "no random_state", "with_mean=False", "n_neighbors <=",
                     "the other way round", "no clipping",
                     # evolve 39698543319 (2026-10-22): 12 of 18 crashes, then 2 more
                     "51,506 x 13,953", "float32", "sklearn.cross_decomposition",
                     # evolve 39713090991 (2026-10-22): 7 broadcast errors, 3 TruncatedSVD dtype, 1 KernelRidge
                     # fit_intercept, and round 1 called StandardScaler a per-cell z-score
                     "no\ndtype argument", "fit_intercept", "keepdims=True", "standardizes columns"):
            self.assertIn(hint, op.BRIEF)

    def test_the_code_is_the_last_python_block_that_defines_predict(self):
        text = "plan\n```python\nx = 1\n```\nthen\n" + GOOD + "\n```python\nprint('usage')\n```"
        self.assertIn("def predict(", op.extract_code(text))
        self.assertIsNone(op.extract_code("no code here"))

    def test_a_candidate_runs_in_a_container_with_no_network_and_only_its_own_inputs(self):
        import os
        from unittest import mock
        with mock.patch.dict(os.environ, {"SB_RUNTIME": "runsc"}):
            cmd = op.docker_cmd("sb-cand-x", "/w/c.py", "/w/val-swap")
        s = " ".join(cmd)
        for flag in ("--network none", "--read-only", "--cap-drop ALL", "--security-opt no-new-privileges",
                     "--runtime runsc", "--log-driver none", f"--memory {op.SANDBOX_MEM}", "--pids-limit"):
            self.assertIn(flag, s)
        mounts = [cmd[i + 1] for i, x in enumerate(cmd) if x == "--mount"]
        self.assertEqual({m.split(",")[1] for m in mounts}, {"src=/w/c.py", "src=/w/val-swap", f"src={op.TOOL}"})
        self.assertTrue(all(m.endswith(",readonly") for m in mounts), "every host path is read-only")
        self.assertNotIn("KUMORI_API_KEY", s)
        self.assertEqual(cmd[-1], "-", "the prediction comes back on stdout, not as a file")

    def test_the_best_is_the_largest_pearson_lead_among_those_that_beat_the_reference_on_both(self):
        # shot 1 (2026-10-21): ranked by rmse, it won rmse on test and lost Pearson; Pearson is the metric we lose
        ref = {"rmse": 0.969, "mean_pearson_per_cell": 0.7855}
        rows = [{"metrics": {"rmse": 0.90, "mean_pearson_per_cell": 0.70}},      # lower rmse, worse Pearson
                {"metrics": {"rmse": 0.93, "mean_pearson_per_cell": 0.79}},      # lowest rmse that qualifies
                {"metrics": {"rmse": 0.96, "mean_pearson_per_cell": 0.80}},      # larger Pearson lead
                {"metrics": {"rmse": 0.97, "mean_pearson_per_cell": 0.81}},      # rmse not below the reference
                {"error": "Traceback"}]
        self.assertIs(op.best(rows, ref), rows[2])
        self.assertIsNone(op.best([rows[0], rows[3], rows[4]], ref))
        tie = {"metrics": {"rmse": 0.90, "mean_pearson_per_cell": 0.7855}}
        self.assertIsNone(op.best([tie], ref), "a tie on Pearson is not a lead")

    def test_the_closest_candidate_is_told_exactly_which_checks_it_fails(self):
        ref = {"rmse": 0.969, "mean_pearson_per_cell": 0.7855, "swap": {"rmse": 0.40, "mean_pearson_per_cell": 0.70}}
        m = {"rmse": 0.94, "mean_pearson_per_cell": 0.79, "swap": {"rmse": 0.45, "mean_pearson_per_cell": 0.71}}
        self.assertEqual(op.failed_checks(m, ref), ["no worse than the reference on the swap direction"])

    def test_the_brief_starts_from_the_published_winner_and_credits_it(self):
        for hint in ("Guanlab-dengkw", "Lance et al.", "z-score", "kernel ridge", "12,000", "average", "no input SVD"):
            self.assertIn(hint, op.BRIEF)
        self.assertIn("Claude Opus", op.BRIEF_ASSIST, "frontier help is labeled with its drafter (the bar)")

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
        rows = op.evolve(3, ask, lambda code: next(scores), ref, writer="fake")
        self.assertTrue(all(r["brief_assist"] == op.BRIEF_ASSIST for r in rows), "every row carries the disclosure")
        self.assertIn("np.ones", asked[1], "the crashed code is shown to be fixed")
        self.assertIn("ValueError: boom", asked[1])
        self.assertIn("0.9400", asked[2], "the closest candidate is shown though its Pearson is below the reference")
        self.assertIn("does not yet pass: Pearson per cell above the reference's", asked[2])


try:
    import sklearn  # noqa: F401
    HAS_SKLEARN = True
except ImportError:
    HAS_SKLEARN = False


class Screen(unittest.TestCase):
    """2026-10-22, evolve 39721561134: 17 of 20 rounds crashed in full scoring, each crash costing a whole round."""
    REF = {"rmse": 0.969, "mean_pearson_per_cell": 0.7855}

    def test_a_screen_crash_goes_back_to_the_writer_and_the_fix_is_what_gets_scored(self):
        asked, scored = [], []
        replies = iter([GOOD, GOOD.replace("np.zeros", "np.ones")])

        def ask(prompt):
            asked.append(prompt)
            return next(replies)
        screen = lambda code: None if "np.ones" in code else "swap direction: exit 1: ValueError: shapes (700,50) (2000,1)"
        rows = op.evolve(1, ask, lambda code: scored.append(code) or {"rmse": 0.95, "mean_pearson_per_cell": 0.79},
                         self.REF, writer="fake", screen=screen, repairs=2)
        self.assertIn("shapes (700,50) (2000,1)", asked[1], "the repair ask carries the traceback")
        self.assertIn("np.zeros", asked[1], "and the code that crashed")
        self.assertEqual(len(scored), 1)
        self.assertIn("np.ones", scored[0], "the repaired code is scored, not the crashed one")
        self.assertEqual((rows[0]["repair_asks"], len(rows[0]["screen_errors"])), (1, 1))
        self.assertIn("metrics", rows[0])

    def test_repairs_are_bounded_and_a_round_that_never_passes_is_not_scored(self):
        asks = []
        rows = op.evolve(1, lambda p: asks.append(p) or GOOD, lambda code: self.fail("scored a screen failure"),
                         self.REF, writer="fake", screen=lambda code: "normal direction: exit 1: boom", repairs=2)
        self.assertEqual(len(asks), 3, "one ask for the round, two repairs, no more")
        self.assertTrue(rows[0]["error"].startswith("screen: normal direction"))
        self.assertEqual(rows[0]["repair_asks"], 2)

    def test_an_ask_budget_counts_repairs_and_stops_the_run(self):
        asks = []
        rows = op.evolve(20, lambda p: asks.append(p) or GOOD, lambda code: {"rmse": 0.95, "mean_pearson_per_cell": 0.79},
                         self.REF, writer="fake", screen=lambda code: "normal direction: exit 1: boom", repairs=2,
                         max_asks=7)
        self.assertEqual(len(asks), 7, "rounds and repairs together never pass the budget")
        self.assertEqual(sum(1 + r.get("repair_asks", 0) for r in rows), 7)

    def test_without_a_screen_rows_are_as_before(self):
        rows = op.evolve(1, lambda p: GOOD, lambda code: {"rmse": 0.95, "mean_pearson_per_cell": 0.79}, self.REF, writer="fake")
        self.assertNotIn("repair_asks", rows[0])

    def test_the_slice_uses_training_cells_only_with_unequal_rows_and_a_held_out_site(self):
        import tempfile
        from scipy import sparse
        rng = np.random.default_rng(0)
        val, d = Path(tempfile.mkdtemp()), Path(tempfile.mkdtemp()) / "screen"
        b = np.array([f"s{2 + i % 3}d1" for i in range(300)])
        op.write_inputs(val, sparse.random(300, 7, density=0.3, format="csr", random_state=0), rng.normal(size=(300, 4)),
                        sparse.csr_matrix(np.ones((50, 7))), b, np.array(["s1d1"] * 50))
        shape = op.screen_inputs(val, d, rows=(120, 40))
        self.assertEqual(shape, (40, 4))
        bt, bs = np.load(d / "batch_train.npy", allow_pickle=True), np.load(d / "batch_test.npy", allow_pickle=True)
        self.assertEqual((len(bt), len(bs)), (120, 40))
        self.assertEqual(set(bs), {"s4d1"}, "test cells come from one training site")
        self.assertNotIn("s4d1", set(bt))
        self.assertNotIn("s1d1", set(bt) | set(bs), "nothing from the held-out validation cells")
        self.assertTrue(sparse.issparse(sparse.load_npz(d / "X_train.npz")))


class SwapValidation(unittest.TestCase):
    @unittest.skipUnless(HAS_SKLEARN, "needs scikit-learn (the openproblems venv)")
    def test_chunked_knnr_equals_the_plain_mean_of_nearest_neighbours(self):
        from sklearn.neighbors import NearestNeighbors
        rng = np.random.default_rng(1)
        Xtr, Ytr, Xte = rng.normal(size=(60, 8)), rng.normal(size=(60, 5)), rng.normal(size=(17, 8))
        emb = lambda X: X                                     # the embedding is fixed here so only the kNN is tested
        got = op.knnr_chunked(Xtr, Ytr, Xte, k=7, chunk=4, embed=lambda a, b: (emb(a), emb(b)))
        idx = NearestNeighbors(n_neighbors=7).fit(Xtr).kneighbors(Xte, return_distance=False)
        np.testing.assert_allclose(got, Ytr[idx].mean(axis=1), rtol=0, atol=1e-6)   # float32 output

    def test_a_candidate_counts_only_if_it_is_also_no_worse_on_swap(self):
        ref = {"rmse": 0.969, "mean_pearson_per_cell": 0.7855, "swap": {"rmse": 0.40, "mean_pearson_per_cell": 0.70}}
        both = {"metrics": {"rmse": 0.94, "mean_pearson_per_cell": 0.79, "swap": {"rmse": 0.39, "mean_pearson_per_cell": 0.71}}}
        one_way = {"metrics": {"rmse": 0.90, "mean_pearson_per_cell": 0.80, "swap": {"rmse": 0.45, "mean_pearson_per_cell": 0.71}}}
        old = {"metrics": {"rmse": 0.89, "mean_pearson_per_cell": 0.81}}                 # scored before swap was
        self.assertIs(op.best([both, one_way, old], ref), both)


    def test_with_a_validation_bootstrap_only_a_lead_clear_of_zero_counts(self):
        # shot 1 (2026-10-21): +0.002 Pearson on validation became -0.020 on test; a point lead is not enough
        ref = {"rmse": 0.969, "mean_pearson_per_cell": 0.7855, "bootstrap": True}
        clear = {"metrics": {"rmse": 0.94, "mean_pearson_per_cell": 0.80,
                             "ci": {"rmse": [-0.03, -0.01], "mean_pearson_per_cell": [0.004, 0.02]}}}
        thin = {"metrics": {"rmse": 0.93, "mean_pearson_per_cell": 0.7876,
                            "ci": {"rmse": [-0.05, -0.02], "mean_pearson_per_cell": [-0.003, 0.007]}}}
        unscored = {"metrics": {"rmse": 0.90, "mean_pearson_per_cell": 0.81}}             # scored before the gate
        self.assertIs(op.best([clear, thin, unscored], ref), clear)
        self.assertIsNone(op.best([thin, unscored], ref))

    def test_the_validation_interval_is_the_bars_paired_bootstrap_against_the_reference(self):
        rng = np.random.default_rng(1)
        y = rng.normal(size=(300, 12))
        ref_pred = y + rng.normal(scale=1.0, size=y.shape)
        cand = y + rng.normal(scale=0.5, size=y.shape)
        ci = op.gate_ci(y, cand, ref_pred, n=500)
        self.assertLess(ci["rmse"][1], 0)
        self.assertGreater(ci["mean_pearson_per_cell"][0], 0)
        self.assertEqual(ci["rmse"], [round(x, 5) for x in op.paired_bootstrap(y, cand, ref_pred, "rmse", n=500)])


class Sandboxed(unittest.TestCase):
    """The streaming protocol, run with plain local Python in place of docker (the same run-candidate code path)."""

    def setUp(self):
        import tempfile
        self.d = Path(tempfile.mkdtemp())
        val = self.d / "in"
        from scipy import sparse
        op.write_inputs(val, sparse.csr_matrix(np.ones((6, 4))), np.ones((6, 3)), sparse.csr_matrix(np.ones((5, 4))),
                        np.array(["s1d1"] * 6), np.array(["s2d1"] * 5))
        self.val, self.shape = val, (5, 3)
        self.cleaned = []

    def go(self, code, timeout=60, cleanup=None):
        f = self.d / "c.py"
        f.write_text(code)
        cmd = [sys.executable, "-I", str(op.TOOL), "run-candidate", str(f), str(self.val), "-"]
        return op.run_sandboxed(cmd, self.shape, timeout, cleanup or (lambda: self.cleaned.append(1)))

    def test_a_prediction_streams_back_whole_even_if_the_candidate_prints(self):
        code = "import numpy as np\ndef predict(a, b, c, d, e):\n    print('debug ' * 999)\n    return np.full((c.shape[0], b.shape[1]), 2.0)\n"
        p, err, _ = self.go(code)
        self.assertIsNone(err)
        self.assertEqual(p.shape, self.shape)
        self.assertTrue((p == 2.0).all())
        self.assertEqual(self.cleaned, [1], "cleanup always runs")

    def test_too_few_or_too_many_bytes_is_the_candidates_error(self):
        short = "import numpy as np\ndef predict(a, b, c, d, e):\n    return np.ones((2, 3))\n"
        p, err, _ = self.go(short)
        self.assertIsNone(p)
        self.assertIn("bytes", err)
        extra = ("import numpy as np, os\ndef predict(a, b, c, d, e):\n"
                 "    os.write(3, b'x' * 64)\n    return np.ones((c.shape[0], b.shape[1]))\n")   # fd 3: the data dup
        p, err, _ = self.go(extra)
        self.assertIsNone(p)

    def test_a_candidate_past_its_time_is_stopped_and_cleaned_up(self):
        slow = "import time\ndef predict(a, b, c, d, e):\n    time.sleep(60)\n"
        p, err, _ = self.go(slow, timeout=2)
        self.assertIsNone(p)
        self.assertIn("over", err)
        self.assertEqual(self.cleaned, [1])

    def test_the_sandbox_check_goes_red_outside_a_sandbox(self):
        # the canary seen failing: run without a container (network open here), the network canary must trip
        from unittest import mock
        def local(code_file, inputs, shape, timeout, dir_mode=0o755, mem=None, diag=None):
            cmd = [sys.executable, "-I", str(op.TOOL), "run-candidate", str(code_file), str(inputs), "-"]
            return op.run_sandboxed(cmd, shape, timeout, lambda: None)
        with mock.patch.object(op, "sandboxed_predict", side_effect=local):
            with self.assertRaises(SystemExit) as e:
                op.sandbox_check(self.d / "chk")
        self.assertIn("network", str(e.exception))

    def test_cleanup_believes_only_dockers_own_no_such_container(self):
        from unittest import mock
        gone = mock.Mock(returncode=1, stderr="Error: No such object: sb-cand-x")
        removed = mock.Mock(returncode=0, stderr="")
        daemon = mock.Mock(returncode=1, stderr="Cannot connect to the Docker daemon at unix:///var/run/docker.sock")
        with mock.patch.object(op.subprocess, "run", side_effect=[removed, gone]):
            op.docker_cleanup("sb-cand-x")                                         # removed, then confirmed absent
        for replies in ([daemon, daemon], [removed, daemon]):
            with mock.patch.object(op.subprocess, "run", side_effect=replies), self.assertRaises(RuntimeError):
                op.docker_cleanup("sb-cand-x")                                     # an API failure is not absence
        with mock.patch.object(op.subprocess, "run", side_effect=op.subprocess.TimeoutExpired("docker", 30)), \
                self.assertRaises(RuntimeError):
            op.docker_cleanup("sb-cand-x")

    def test_a_client_that_will_not_exit_still_gets_its_container_cleaned_up(self):
        import io
        from unittest import mock
        proc = mock.Mock(stdout=io.BytesIO(b""), stderr=io.BytesIO(b""))
        proc.poll.return_value = None
        proc.wait.side_effect = op.subprocess.TimeoutExpired("docker", 30)
        cleaned = []
        with mock.patch.object(op.subprocess, "Popen", return_value=proc), self.assertRaises(RuntimeError):
            op.run_sandboxed(["docker"], (5, 3), 1, lambda: cleaned.append(1))
        self.assertEqual(cleaned, [1], "cleanup runs before the hang is reported")

    def test_a_cleanup_that_cannot_confirm_the_container_is_gone_fails_the_run(self):
        def bad():
            raise RuntimeError("container still there")
        with self.assertRaises(RuntimeError):
            self.go("import numpy as np\ndef predict(a, b, c, d, e):\n    return np.ones((5, 3))\n", cleanup=bad)


class Qualify(unittest.TestCase):
    """Leave-one-site-out before any test scoring (DECISIONS 2026-10-22): every training site held out in turn, both
    directions; the candidate must beat the reference on rmse and Pearson at every site."""

    def test_sites_come_from_the_batch_names_and_a_bad_name_stops_it(self):
        self.assertEqual(op.sites_of(np.array(["s2d1", "s1d3", "s1d1", "s3d7"])), [1, 2, 3])
        with self.assertRaises(ValueError):
            op.sites_of(np.array(["s1d1", "donor7"]))

    def test_the_verdict_needs_a_strict_win_at_every_site_and_no_error(self):
        win = {"error": None, "cand": {"rmse": 0.9, "mean_pearson_per_cell": 0.8},
               "ref": {"rmse": 1.0, "mean_pearson_per_cell": 0.7}}
        tie = {**win, "cand": {"rmse": 0.9, "mean_pearson_per_cell": 0.7}}
        err = {**win, "error": "exit 137"}
        self.assertTrue(op.qualify_verdict([win, win])["passed"])
        self.assertFalse(op.qualify_verdict([win, tie])["passed"], "a tie on Pearson at one site is not a lead")
        self.assertFalse(op.qualify_verdict([win, err])["passed"], "an execution failure is not a pass")
        self.assertFalse(op.qualify_verdict([])["passed"], "no sites, no qualification")
        v = op.qualify_verdict([win, {**win, "cand": {"rmse": 0.95, "mean_pearson_per_cell": 0.75}}])
        self.assertAlmostEqual(v["worst_pearson_delta"], 0.05)
        self.assertAlmostEqual(v["mean_pearson_delta"], 0.075)

    def test_each_held_out_site_is_scored_against_the_reference_on_that_site(self):
        rng = np.random.default_rng(0)
        X = rng.normal(size=(40, 6)); Y = X[:, :3] * 2 + rng.normal(scale=0.1, size=(40, 3))
        batches = np.array([f"s{1 + i % 2}d1" for i in range(40)])
        seen = []
        def fake(code_file, inputs, shape, timeout, dir_mode=0o755, mem=None, diag=None):
            seen.append(shape)
            assert mem == op.QUALIFY_MEM
            return np.zeros(shape, dtype=np.float32), None, ""
        import tempfile
        rows = op.qualify_direction(X, Y, batches, Path(tempfile.mkdtemp()), Path("c.py"), predict=fake,
                                    reference=lambda a, b, c: np.zeros((c.shape[0], b.shape[1])))
        self.assertEqual([r["site"] for r in rows], [1, 2])
        self.assertEqual(seen, [(20, 3), (20, 3)])
        self.assertTrue(all(r["error"] is None and "rmse" in r["cand"] for r in rows))

    def test_each_fold_records_how_its_container_ended(self):
        """2026-10-22, qualify 39721557552: swap site 3 died with exit 137 and the receipt could not say whose kill."""
        X = np.arange(40 * 4, dtype=float).reshape(40, 4); Y = X[:, :2]
        batches = np.array([f"s{1 + i % 2}d1" for i in range(40)])
        def fake(code_file, inputs, shape, timeout, dir_mode=0o755, mem=None, diag=None):
            diag.update(mem_peak_gb_seen=9.9, oom_killed=True, exit_code=137, mem_cap=mem)
            return None, "exit 137: ", ""
        import tempfile
        rows = op.qualify_direction(X, Y, batches, Path(tempfile.mkdtemp()), Path("c.py"), predict=fake,
                                    reference=lambda a, b, c: np.zeros((c.shape[0], b.shape[1])))
        self.assertEqual(rows[0]["container"], {"mem_peak_gb_seen": 9.9, "oom_killed": True, "exit_code": 137,
                                                "mem_cap": op.QUALIFY_MEM})

    def test_every_stage_gives_a_candidate_the_same_memory(self):
        self.assertEqual(op.QUALIFY_MEM, op.SANDBOX_MEM)
        self.assertIn(f"{op.SANDBOX_MEM[:-1]} GiB budget", op.BRIEF, "the writer is told the cap it will get")

    def test_host_memory_is_watched_while_the_candidate_runs(self):
        import os
        stop = op.host_rss_watch(every=0.01)
        held = np.ones(1 << 24)                          # 128 MiB, touched
        gb = stop()
        if not os.path.exists("/proc/self/status"):
            self.assertIsNone(gb)
        else:
            self.assertGreater(gb, 0.1)
        del held

    def test_container_exit_reads_dockers_oom_flag(self):
        from unittest import mock
        done = lambda out: mock.Mock(stdout=out, returncode=0)
        with mock.patch.object(op.subprocess, "run", return_value=done("true 137\n")):
            self.assertEqual(op.container_exit("x"), {"oom_killed": True, "exit_code": 137})
        with mock.patch.object(op.subprocess, "run", return_value=done("false 137\n")):
            self.assertEqual(op.container_exit("x"), {"oom_killed": False, "exit_code": 137})
        with mock.patch.object(op.subprocess, "run", return_value=done("")):         # already gone: unknown, not a guess
            self.assertEqual(op.container_exit("x"), {"oom_killed": None, "exit_code": None})

    def test_a_failing_diagnostic_never_skips_the_containers_removal(self):
        from unittest import mock
        removed = []
        def run(cmd, shape, timeout, cleanup):
            cleanup()
            return None, "exit 137: ", ""
        import tempfile
        d = Path(tempfile.mkdtemp()); (d / "x").write_text("x"); c = d / "c.py"; c.write_text("")
        with mock.patch.object(op, "run_sandboxed", run), \
                mock.patch.object(op, "container_exit", side_effect=OSError("docker gone")), \
                mock.patch.object(op, "docker_cleanup", side_effect=removed.append), \
                mock.patch.object(op, "container_memory", lambda *a: None):
            with self.assertRaises(OSError):
                op.sandboxed_predict(c, d, (1, 1), 5)
        self.assertEqual(len(removed), 1)

    def test_the_container_is_not_auto_removed_before_its_exit_is_read(self):
        self.assertNotIn("--rm", op.docker_cmd("n", Path("/c.py"), Path("/in")))

    def _fold(self, site, lost=None, error=None):
        """A receipt row; `lost` names the metric(s) the candidate did not win at this site."""
        lost = lost or ()
        cand = {"rmse": 0.95 if "rmse" in lost else 0.9, "mean_pearson_per_cell": 0.7 if "pearson" in lost else 0.8}
        return {"site": site, "error": error, "cand": None if error else cand,
                "ref": {"rmse": 0.92, "mean_pearson_per_cell": 0.75}}

    def _receipt(self, normal, swap, code_sha="s", at="2026-11-01"):
        return {"at": at, "code_sha": code_sha, "source": {"evolve_file": "f", "round": 1}, "policy": op.QUALIFY_POLICY,
                "rows": {"normal": normal, "swap": swap}, "expected_sites": {"normal": [1, 2, 3], "swap": [1, 2, 3]}}

    def test_the_screen_runs_the_folds_recent_receipts_lost_first(self):
        """2026-10-22..11-01: all 8 receipts lost normal/site 2 (rmse), run second of six, after 7-19 min of folds."""
        full = lambda *lost_at: [self._fold(s, lost=("rmse",) if ("normal", s) in lost_at else ()) for s in (1, 2, 3)]
        swap_ok = [self._fold(s) for s in (1, 2, 3)]
        r1 = self._receipt(full(("normal", 2), ("normal", 3)), swap_ok, "a", "2026-10-30")
        r2 = self._receipt(full(("normal", 2)), swap_ok, "b", "2026-10-31")
        r3 = self._receipt(full(("normal", 2), ("normal", 3)), [self._fold(1), self._fold(2, error="exit 137"), self._fold(3)], "c", "2026-11-01")
        old = self._receipt(full(("normal", 1)), swap_ok, "d", "2026-10-22")
        self.assertEqual(op.screen_folds([old, r1, r2, r3], n=3), [("normal", 2), ("normal", 3), ("swap", 2)],
                         "most often lost first, from the latest three complete receipts only")
        self.assertEqual(op.screen_folds([], n=3), [])
        partial = dict(r1, rows={"normal": r1["rows"]["normal"]})
        self.assertEqual(op.screen_folds([partial], n=3), [], "an incomplete receipt does not choose the screen")

    def test_a_lost_screen_fold_ends_the_direction_and_the_order_is_the_screens(self):
        rng = np.random.default_rng(0)
        X = rng.normal(size=(60, 6)); Y = X[:, :3]
        batches = np.array([f"s{1 + i % 3}d1" for i in range(60)])
        import tempfile
        ref = lambda a, b, c: np.zeros((c.shape[0], b.shape[1]))
        def loses_at_2(code_file, inputs, shape, timeout, dir_mode=0o755, mem=None, diag=None):
            site = int(Path(inputs).parent.name[4:])
            return (np.ones(shape, dtype=np.float32) if site == 2 else np.zeros(shape, dtype=np.float32)), None, ""
        rows = op.qualify_direction(X, Y, batches, Path(tempfile.mkdtemp()), Path("c.py"), predict=loses_at_2,
                                    reference=ref, sites=[2, 3, 1], stop_on_loss=True)
        self.assertEqual([r["site"] for r in rows], [2], "stopped at the first lost fold")
        def wins(code_file, inputs, shape, timeout, dir_mode=0o755, mem=None, diag=None):   # the answer itself: Y = X[:, :3]
            from scipy import sparse
            return sparse.load_npz(Path(inputs) / "X_test.npz").toarray()[:, :3].astype(np.float32), None, ""
        rows = op.qualify_direction(X, Y, batches, Path(tempfile.mkdtemp()), Path("c.py"), predict=wins,
                                    reference=ref, sites=[2, 3, 1], stop_on_loss=True)
        self.assertEqual([r["site"] for r in rows], [2, 3, 1], "no loss: every fold, in the screen's order")
        rows = op.qualify_direction(X, Y, batches, Path(tempfile.mkdtemp()), Path("c.py"), predict=loses_at_2, reference=ref)
        self.assertEqual([r["site"] for r in rows], [1, 2, 3], "defaults unchanged: every site ascending, no stop")

    def test_a_screened_out_receipt_can_never_pass_and_is_still_measured(self):
        import tempfile
        d = Path(tempfile.mkdtemp())
        rows = {"normal": [self._fold(2, lost=("rmse",))]}
        r = op.write_receipt(d / "qualify-1.json", {"evolve_file": "f", "round": 1}, "code", rows,
                             expected={"normal": [1, 2, 3], "swap": [1, 2, 3]},
                             screen={"folds": [["normal", 2], ["normal", 3]], "stopped_at": "normal/2"})
        self.assertFalse(r["verdict"]["passed"])
        self.assertEqual(r["screen"]["stopped_at"], "normal/2")
        self.assertFalse(op.receipt_complete(r))
        with self.assertRaises(SystemExit):
            op.check_qualified(d, {"evolve_file": "f", "round": 1}, "code")
        by_file = {"f": [{"round": 1, "code": "code", "metrics": M, "reference": {"normal": REF}}]}
        self.assertIsNone(op.next_qualify(by_file, [r]), "a screened-out candidate is measured: never picked again")
        with self.assertRaises(AssertionError):
            op.write_receipt(d / "qualify-2.json", {"evolve_file": "f", "round": 1}, "code", {"normal": [self._fold(2)]},
                             expected={"normal": [1, 2, 3], "swap": [1, 2, 3]}, screen={"folds": [["normal", 2]], "stopped_at": "normal/2"})

    def test_the_brief_still_names_the_misses_of_a_screened_out_seed(self):
        r = self._receipt([self._fold(2, lost=("rmse",))], [])
        r["screen"] = {"folds": [["normal", 2], ["normal", 3]], "stopped_at": "normal/2"}
        note = op.loso_note(r)
        self.assertIn("site 2", note)
        self.assertIn("rmse", note)
        self.assertIn("stopped at that fold", note)
        self.assertNotIn("passed every site", note)
        self.assertIsNone(op.loso_note(dict(r, screen=None, rows={"normal": r["rows"]["normal"]})), "incomplete without a screen: not a verdict")

    def test_qualify_holds_one_directions_matrices_at_a_time_and_stops_the_run_on_a_lost_screen_fold(self):
        """Codex 20261102T201458287126Z f4: X and Y of the normal direction must be collectable before the swap files load."""
        import gc, sys, tempfile, types, weakref
        from unittest import mock
        alive, calls = [], []
        class Fake:
            def __init__(self, n):
                self.obs = {"batch": types.SimpleNamespace(astype=lambda t: types.SimpleNamespace(values=np.array([f"s{1 + i % 3}d1" for i in range(n)])))}
                self.layers = {"normalized": np.zeros((n, 4))}
        def read_h5ad(path):
            if "swap" in str(path):
                gc.collect()
                self.assertTrue(all(r() is None for d, r in alive if d == "normal"), "the normal direction's matrices are still alive at the swap read")
            f = Fake(30)
            alive.append(("swap" if "swap" in str(path) else "normal", weakref.ref(f.layers["normalized"])))
            return f
        def direction(X, Y, b, work, code_file, sites=None, stop_on_loss=False, **kw):
            calls.append((str(work)[-12:], list(sites) if sites is not None else None, stop_on_loss))
            lost = stop_on_loss and sites == [2] and "swap" in str(work)
            return [{"site": s, "error": None, "cand": {"rmse": 0.95 if lost else 0.9, "mean_pearson_per_cell": 0.8},
                     "ref": {"rmse": 0.92, "mean_pearson_per_cell": 0.75}} for s in (sites or [1, 2, 3])]
        d = Path(tempfile.mkdtemp())
        with mock.patch.dict(sys.modules, {"anndata": types.SimpleNamespace(read_h5ad=read_h5ad)}), \
                mock.patch.object(op, "download", lambda *a, **k: None), \
                mock.patch.object(op, "qualify_direction", direction):
            op.qualify(d, "code", {"evolve_file": "f", "round": 1}, d / "r.json", screen=[("normal", 2), ("swap", 2)])
        r = json.loads((d / "r.json").read_text())
        self.assertEqual(calls, [("normal-folds", [2], True), ("normal-folds", [1, 3], False), ("q-swap-folds", [2], True)])
        self.assertEqual(r["screen"], {"folds": [["normal", 2], ["swap", 2]], "stopped_at": "swap/2"})
        self.assertFalse(r["verdict"]["passed"]); self.assertFalse(op.receipt_complete(r))
        self.assertEqual([x["site"] for x in r["rows"]["normal"]], [2, 1, 3])
        self.assertEqual([x["site"] for x in r["rows"]["swap"]], [2])

    def test_a_shot_needs_a_passing_receipt_for_this_exact_code_and_policy(self):
        import tempfile
        led = Path(tempfile.mkdtemp())
        src = {"evolve_file": "e.jsonl", "round": 4}
        win = {"site": 1, "error": None, "cand": {"rmse": 0.9, "mean_pearson_per_cell": 0.8},
               "ref": {"rmse": 1.0, "mean_pearson_per_cell": 0.7}}
        with self.assertRaises(SystemExit):
            op.check_qualified(led, src, "code")                                  # none
        op.write_receipt(led / "qualify-1.json", src, "code", {"normal": [win], "swap": [win]})
        op.check_qualified(led, src, "code")
        with self.assertRaises(SystemExit):
            op.check_qualified(led, src, "other code")
        lose = {**win, "cand": {"rmse": 1.1, "mean_pearson_per_cell": 0.8}}
        op.write_receipt(led / "qualify-2.json", {**src, "round": 5}, "c5", {"normal": [win], "swap": [lose]})
        with self.assertRaises(SystemExit):
            op.check_qualified(led, {**src, "round": 5}, "c5")                    # a failing receipt
        r = json.loads((led / "qualify-1.json").read_text())
        part = {**r, "rows": {"normal": [win]}}                                   # a direction missing
        (led / "qualify-3.json").write_text(json.dumps({**part, "source": {**src, "round": 7}}))
        with self.assertRaises(SystemExit):
            op.check_qualified(led, {**src, "round": 7}, "code")
        short = {**r, "source": {**src, "round": 8}, "expected_sites": {"normal": [1, 2], "swap": [1, 2]}}
        (led / "qualify-4.json").write_text(json.dumps(short))                     # site 2 never scored
        with self.assertRaises(SystemExit):
            op.check_qualified(led, {**src, "round": 8}, "code")
        r["verdict"]["passed"] = True
        r["rows"]["swap"] = [lose]; (led / "qualify-1.json").write_text(json.dumps(r))
        with self.assertRaises(SystemExit):
            op.check_qualified(led, src, "code")                                  # verdict recomputed from rows


class Pin(unittest.TestCase):
    """The upstream pin (2026-11-03): upstream bc9313f98a added par['seed'] at 14:12 UTC and our 16:42 run, which read
    upstream main, died on it (run 41676849790). Every fetch reads one full SHA; a newer main is checked, never used."""
    REF = {"rmse": 0.9688, "mae": 0.6669, "mean_pearson_per_cell": 0.7858, "pred_fp": "0" * 64,
           "swap": {"rmse": 0.3229, "mae": 0.1554, "mean_pearson_per_cell": 0.7497}}

    def test_every_fetch_reads_the_pinned_full_sha_and_only_the_drift_check_reads_main(self):
        self.assertRegex(op.UPSTREAM_SHA, r"^[0-9a-f]{40}$")
        src = Path(op.__file__).read_text()
        self.assertEqual(src.count("commits/main"), 1, "upstream main is read in one place, upstream_main()")
        self.assertFalse(hasattr(op, "pinned_sha"))

    def test_the_swap_reference_is_seeded_like_the_normal_one(self):
        import inspect
        self.assertEqual(inspect.signature(op.knnr_chunked).parameters["random_state"].default, 0)

    def test_a_reference_is_the_same_within_its_tolerance_and_both_directions(self):
        row = {"reference": {"knnr_py": dict(self.REF)}}
        self.assertTrue(op.same_reference(row, self.REF))
        near = {**self.REF, "rmse": self.REF["rmse"] + 0.00005}
        self.assertTrue(op.same_reference(row, near))
        self.assertFalse(op.same_reference(row, {**self.REF, "rmse": self.REF["rmse"] + 0.0007}),
                         "the unseeded reference moved ~0.1% between runs (DECISIONS 2026-10-20): another reference")
        self.assertFalse(op.same_reference(row, {**self.REF, "swap": {**self.REF["swap"], "mean_pearson_per_cell": 0.75}}))
        self.assertFalse(op.same_reference({"reference": {"knnr_py": {"rmse": 0.9688}}}, self.REF), "no swap: not comparable")
        self.assertFalse(op.same_reference({}, self.REF))

    def _old(self, pearson, code, ci=True):
        old_ref = {**self.REF, "rmse": 0.9695, "bootstrap": True}
        return {"at": "2026-11-02T22:41:35+00:00", "round": 3, "code": code, "reference": {"knnr_py": old_ref},
                "metrics": {"rmse": 0.95, "mae": 0.66, "mean_pearson_per_cell": pearson,
                            "swap": {"rmse": 0.32, "mae": 0.15, "mean_pearson_per_cell": 0.75},
                            **({"ci": {"rmse": [-0.02, -0.01], "mean_pearson_per_cell": [0.001, 0.01]}} if ci else {})}}

    def test_rows_scored_against_another_reference_never_seed_on_their_old_interval(self):
        """Codex 20261103T184829013094Z f2: best() took an old row's bootstrap interval, computed against that run's
        reference predictions, as a lead over today's reference."""
        ref = {**self.REF, "bootstrap": True}
        prior = [self._old(0.79, "OLD_BEST"), self._old(0.788, "OLD_NEXT")]
        scored = []

        def score(code):
            scored.append(code)
            return {"rmse": 0.96, "mae": 0.66, "mean_pearson_per_cell": 0.7859,
                    "swap": {"rmse": 0.32, "mae": 0.15, "mean_pearson_per_cell": 0.75},
                    "ci": {"rmse": [-0.01, 0.002], "mean_pearson_per_cell": [-0.001, 0.002]}}
        seed, row = op.seed_for(prior, ref, score)
        self.assertEqual(scored, ["OLD_BEST"], "one rescore, of the old best, on today's split and reference")
        self.assertEqual(seed["code"], "OLD_BEST")
        self.assertEqual(seed["metrics"]["mean_pearson_per_cell"], 0.7859, "today's numbers, not the old row's")
        self.assertIsNone(op.best([seed], ref), "its new interval crosses zero, so it no longer passes")
        self.assertTrue(row["rescore"] and row["round"] == -1 and row is seed)
        self.assertEqual(row["rescore"]["metrics_then"]["mean_pearson_per_cell"], 0.79)

    def test_a_compatible_row_seeds_as_written_and_nothing_is_rescored(self):
        ref = {**self.REF, "bootstrap": True}
        same = self._old(0.787, "SAME_REF")
        same["reference"]["knnr_py"] = dict(ref)
        seed, row = op.seed_for([self._old(0.79, "OLD_BEST"), same], ref, lambda code: self.fail("no rescore"))
        self.assertEqual(seed["code"], "SAME_REF")
        self.assertIsNone(row)

    def test_a_rescore_that_crashes_seeds_nothing_and_is_recorded(self):
        seed, row = op.seed_for([self._old(0.79, "OLD_BEST")], {**self.REF, "bootstrap": True}, lambda code: {"error": "boom"})
        self.assertIsNone(seed)
        self.assertEqual(row["error"], "boom")
        self.assertTrue(row["rescore"])
        self.assertEqual(op.seed_for([], self.REF, lambda c: self.fail("nothing to rescore")), (None, None))

    def test_the_drift_check_runs_the_gate_at_main_and_records_it_once(self):
        import tempfile
        d = Path(tempfile.mkdtemp())
        calls = []
        same = op.drift(d, d, main=lambda: op.UPSTREAM_SHA, gate=lambda sha: calls.append(sha))
        self.assertEqual((same["status"], calls), ("current", []))
        new = "f" * 40
        r = op.drift(d, d, main=lambda: new, gate=lambda sha: calls.append(sha) or {"pass": True, "metrics": {}})
        self.assertEqual((r["status"], calls, r["main"], r["pinned"]), ("passes", [new], new, op.UPSTREAM_SHA))
        self.assertTrue((d / f"drift-{new[:12]}.json").exists())
        self.assertIsNone(op.drift(d, d, main=lambda: new, gate=lambda sha: self.fail("checked once per commit")))

    def test_equal_metrics_from_other_reference_predictions_are_not_the_same_reference(self):
        """Codex 20261103T185822469055Z f2: two reference predictions with identical aggregate metrics gave a bar-pass
        on reuse and a miss on rescore; the interval is bound to the predictions, so identity is their fingerprint."""
        rng = np.random.default_rng(0)
        a = rng.normal(size=(50, 8)).astype(np.float32)
        ref = {**self.REF, "bootstrap": True, "pred_fp": op.pred_fp(a)}
        noisy = a + rng.normal(scale=1e-6, size=a.shape).astype(np.float32)
        self.assertTrue(op.same_fp(op.pred_fp(a.copy()), op.pred_fp(a)))
        self.assertFalse(op.same_fp(op.pred_fp(noisy), op.pred_fp(a)), "any difference rescores (Codex 20261103T190328625747Z f2)")
        self.assertFalse(op.same_fp(op.pred_fp(a[::-1]), op.pred_fp(a)), "the same values on other cells are another reference")
        self.assertFalse(op.same_fp(op.pred_fp(a.reshape(8, 50)), op.pred_fp(a)))
        self.assertFalse(op.same_fp(None, op.pred_fp(a)))
        same = {"reference": {"knnr_py": dict(ref)}}
        self.assertTrue(op.same_reference(same, ref))
        self.assertFalse(op.same_reference({"reference": {"knnr_py": {**ref, "pred_fp": op.pred_fp(a[::-1])}}}, ref))
        self.assertFalse(op.same_reference({"reference": {"knnr_py": {k: v for k, v in ref.items() if k != "pred_fp"}}}, ref),
                         "a row from before fingerprints is rescored, never trusted")

    def test_codexs_knife_edge_reference_is_rescored_and_fails(self):
        """Codex 20261103T190328625747Z f2, its reproducer verbatim in substance: references 2.4e-7 apart in rmse; the
        old interval passed the bar, the rescored one does not, so the old one must never be reused."""
        rng = np.random.default_rng(17)
        y = rng.normal(size=(50, 20)).astype(np.float32)
        e = rng.normal(size=y.shape).astype(np.float32)
        a, p = y + e, y + e * .99997
        b = a + np.random.default_rng(9).normal(scale=1e-4, size=a.shape).astype(np.float32)
        swap = {"rmse": 1., "mae": .5, "mean_pearson_per_cell": .5}
        ref = lambda x: {**op.metrics(y, x), "swap": swap, "bootstrap": True, "pred_fp": op.pred_fp(x)}
        old, new = ref(a), ref(b)
        m = {**op.metrics(y, p), "swap": swap, "ci": op.gate_ci(y, p, a)}
        row = {"round": 0, "code": "candidate", "reference": {"knnr_py": old}, "metrics": m}
        fresh = {**m, "ci": op.gate_ci(y, p, b)}
        self.assertTrue(op.passes_bar(row, new), "the canary: reusing the old interval would pass")
        calls = []
        seed, _ = op.seed_for([row], new, lambda code: calls.append(code) or fresh)
        self.assertEqual(calls, ["candidate"])
        self.assertFalse(op.passes_bar(seed, new))

    def test_the_reproduce_gate_needs_every_published_metric(self):
        """Codex 20261103T185822469055Z f4: compare() judged the intersection, so a missing correlation output passed."""
        pub = {"rmse": 0.7233, "mae": 0.5255, "mean_pearson_per_cell": 0.7707}
        r = op.compare({"rmse": 0.7234, "mae": 0.5256}, pub)
        self.assertFalse(r["pass"])
        self.assertEqual(r["missing"], ["mean_pearson_per_cell"])
        self.assertTrue(op.compare({"rmse": 0.7234, "mae": 0.5256, "mean_pearson_per_cell": 0.7708, "extra": 1.0}, pub)["pass"])

    def test_a_drift_that_crashes_or_misses_the_gate_fails(self):
        import tempfile
        d = Path(tempfile.mkdtemp())

        def crash(sha):
            raise KeyError("seed")
        r = op.drift(d, d, main=lambda: "a" * 40, gate=crash)
        self.assertEqual(r["status"], "fails")
        self.assertIn("KeyError", r["error"])
        r = op.drift(d, d, main=lambda: "b" * 40, gate=lambda sha: {"pass": False, "metrics": {"rmse": {"diff_pct": 3.0}}})
        self.assertEqual(r["status"], "fails")


class BothWays(unittest.TestCase):
    def test_a_swap_crash_reports_which_way_with_the_normal_scores(self):
        normal = lambda c: {"rmse": 0.94, "mean_pearson_per_cell": 0.79}
        crash = lambda c: {"error": "ValueError: n_components=200 must be <= n_features=134"}
        r = op.both_ways(normal, crash)("code")
        self.assertIn("normal direction ran (rmse 0.9400", r["error"])
        self.assertIn("swap direction crashed: ValueError: n_components=200", r["error"])
        ok = op.both_ways(normal, lambda c: {"rmse": 0.38, "mean_pearson_per_cell": 0.72})("code")
        self.assertEqual(ok["swap"]["rmse"], 0.38)
        self.assertIn("swap direction: rmse 0.3800", op._fmt(ok))


class Final(unittest.TestCase):
    def test_the_verdict_is_the_pre_registered_bar(self):
        normal = {"rmse": {"cand": 0.70, "ref": 0.7233, "ci": (-0.03, -0.01)},
                  "mean_pearson_per_cell": {"cand": 0.79, "ref": 0.7707, "ci": (0.005, 0.03)}}
        swap_ok = {"cand": {"rmse": 0.349, "mean_pearson_per_cell": 0.736}, "ref": {"rmse": 0.3502, "mean_pearson_per_cell": 0.7351}}
        v = op.verdict(normal, swap_ok)
        self.assertEqual((v["useful"], v["competitive"]), (True, False))
        self.assertFalse(op.verdict({**normal, "rmse": {**normal["rmse"], "ci": (-0.03, 0.002)}}, swap_ok)["useful"],
                         "an rmse interval touching zero is not a win")
        swap_bad = {**swap_ok, "cand": {"rmse": 0.50, "mean_pearson_per_cell": 0.736}}
        self.assertFalse(op.verdict(normal, swap_bad)["useful"], "worse on swap fails the bar")
        best = {"rmse": {"cand": 0.66, "ref": 0.7233, "ci": (-0.08, -0.05)},
                "mean_pearson_per_cell": {"cand": 0.80, "ref": 0.7707, "ci": (0.02, 0.04)}}
        self.assertTrue(op.verdict(best, swap_ok)["competitive"])

    def test_no_more_than_three_test_scorings(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            for i in range(3):
                self.assertTrue(op.shot_left(Path(d)))
                (Path(d) / f"final-{i}.json").write_text("{}")
            self.assertFalse(op.shot_left(Path(d)))

    def test_a_reserved_shot_counts_even_if_its_run_died_before_a_result(self):
        # final() wrote final-*.json only after scoring; a runner lost after reading the test set left no count
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            led = Path(d)
            (led / "final-1.json").write_text("{}")
            (led / "shot-1.json").write_text("{}")                          # reserved, then scored: one shot
            (led / "shot-2.json").write_text("{}")                          # reserved, run died: still a shot
            self.assertEqual(op.shots_used(led), 2)
            win = {"site": 1, "error": None, "cand": {"rmse": 0.9, "mean_pearson_per_cell": 0.8}, "ref": {"rmse": 1.0, "mean_pearson_per_cell": 0.7}}
            for rnd in (4, 5):
                op.write_receipt(led / f"qualify-{rnd}.json", {"evolve_file": "e.jsonl", "round": rnd}, "code",
                                 {"normal": [win], "swap": [win]})
            op.reserve(led, "3", {"evolve_file": "e.jsonl", "round": 4}, "code")
            self.assertEqual(op.shots_used(led), 3)
            with self.assertRaises(SystemExit):
                op.reserve(led, "4", {"evolve_file": "e.jsonl", "round": 5}, "code")

    def test_the_test_set_is_read_only_under_this_runs_reservation_for_this_candidate(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            led = Path(d)
            src = {"evolve_file": "e.jsonl", "round": 4}
            with self.assertRaises(SystemExit):
                op.check_reservation(led / "final-9.json", src, "code")          # none
            with self.assertRaises(SystemExit):
                op.reserve(led, "9", src, "code")                                # not qualified: no shot
            win = {"site": 1, "error": None, "cand": {"rmse": 0.9, "mean_pearson_per_cell": 0.8}, "ref": {"rmse": 1.0, "mean_pearson_per_cell": 0.7}}
            op.write_receipt(led / "qualify-9.json", src, "code", {"normal": [win], "swap": [win]})
            op.reserve(led, "9", src, "code")
            op.check_reservation(led / "final-9.json", src, "code")              # passes
            with self.assertRaises(SystemExit):
                op.check_reservation(led / "final-9.json", {**src, "round": 5}, "code")
            with self.assertRaises(SystemExit):
                op.check_reservation(led / "final-9.json", src, "other code")

    def test_a_candidate_comes_from_its_ledger_round(self):
        import tempfile, json
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "evolve-1.jsonl"
            f.write_text(json.dumps({"round": 6, "code": "def predict(): pass\n", "metrics": {"rmse": 0.94}}) + "\n"
                         + json.dumps({"round": 7, "error": "x"}) + "\n")
            self.assertEqual(op.candidate_from(f, 6), "def predict(): pass\n")
            with self.assertRaises(ValueError):
                op.candidate_from(f, 7)



class NextQualify(unittest.TestCase):
    """The scheduled qualify (2026-10-28): the best candidate by the bar's own rule, across every evolve file, whose
    exact code has no qualify receipt yet; nothing when none is new. Rows and receipts are stand-ins."""
    REF = {"rmse": 1.0, "mean_pearson_per_cell": 0.70}

    def rows(self):
        good = lambda rnd, pear, code: {"round": rnd, "code": code, "reference": {"knnr_py": self.REF},
                                        "metrics": {"rmse": 0.9, "mean_pearson_per_cell": pear}}
        return {"ledger/openproblems/evolve-1.jsonl": [good(0, 0.72, "a"), {"round": 1, "error": "crash"}],
                "ledger/openproblems/evolve-2.jsonl": [good(0, 0.75, "b"), good(1, 0.71, "c")]}

    def test_the_best_unqualified_candidate_by_pearson(self):
        pick = op.next_qualify(self.rows(), [])
        self.assertEqual((pick["evolve_file"], pick["round"]), ("ledger/openproblems/evolve-2.jsonl", 0))

    def test_a_candidate_with_a_receipt_for_its_exact_code_is_skipped(self):
        import hashlib
        receipts = [{"code_sha": hashlib.sha256(b"b").hexdigest(), "verdict": {"passed": False}}]
        pick = op.next_qualify(self.rows(), receipts)
        self.assertEqual((pick["evolve_file"], pick["round"]), ("ledger/openproblems/evolve-1.jsonl", 0))

    def test_nothing_new_is_none(self):
        import hashlib
        receipts = [{"code_sha": hashlib.sha256(c.encode()).hexdigest()} for c in "abc"]
        self.assertIsNone(op.next_qualify(self.rows(), receipts))

    def test_a_candidate_below_the_bar_is_never_picked(self):
        rows = {"ledger/openproblems/evolve-3.jsonl": [{"round": 0, "code": "z", "reference": {"knnr_py": self.REF},
                                                        "metrics": {"rmse": 1.2, "mean_pearson_per_cell": 0.80}}]}
        self.assertIsNone(op.next_qualify(rows, []))


M = {"rmse": 0.9259, "mae": 0.6437, "mean_pearson_per_cell": 0.8238, "swap": {"rmse": 0.3115, "mae": 0.1566, "mean_pearson_per_cell": 0.7688}}
REF = {"rmse": 0.9688, "mean_pearson_per_cell": 0.7856, "swap": {"rmse": 0.3229, "mean_pearson_per_cell": 0.7497}}


class SameMethod(unittest.TestCase):
    """2026-10-29..31: three daily qualify runs measured one method three times (identical validation metrics, code
    differing by comments and max(1, ...) guards) because the receipt was keyed on the exact code; evolve had re-emitted
    its own seed each day. The method's behavior on validation is the identity, not its text."""

    def rows(self, code_b="b", metrics_b=M):
        a = {"round": 7, "code": "a", "metrics": M, "reference": {"knnr": REF}}
        b = {"round": 2, "code": code_b, "metrics": metrics_b, "reference": {"knnr": REF}}
        return {"ledger/openproblems/evolve-1.jsonl": [a], "ledger/openproblems/evolve-2.jsonl": [b]}

    def test_qualify_never_remeasures_the_same_program_and_takes_a_lookalike_only_when_nothing_is_fresh(self):
        import hashlib
        receipt = {"source": {"evolve_file": "ledger/openproblems/evolve-1.jsonl", "round": 7},
                   "code_sha": hashlib.sha256(b"x = 1").hexdigest(), "policy": op.QUALIFY_POLICY}
        rows = self.rows(code_b="x = 1  # the seed again, in other words")
        rows["ledger/openproblems/evolve-1.jsonl"][0]["code"] = "x = 1"
        self.assertIsNone(op.next_qualify(rows, [receipt]), "the same program with a new comment is not new")
        rows = self.rows(code_b="x = max(1, 1)")           # another program, the same numbers on site 1
        rows["ledger/openproblems/evolve-1.jsonl"][0]["code"] = "x = 1"
        self.assertEqual(op.next_qualify(rows, [receipt]), {"evolve_file": "ledger/openproblems/evolve-2.jsonl", "round": 2},
                         "a lookalike stays eligible: site 1 alone cannot prove it behaves the same on the other sites")
        rows["ledger/openproblems/evolve-3.jsonl"] = [{"round": 0, "code": "y", "reference": {"knnr": REF},
                                                      "metrics": dict(M, mean_pearson_per_cell=0.8000)}]
        self.assertEqual(op.next_qualify(rows, [receipt]), {"evolve_file": "ledger/openproblems/evolve-3.jsonl", "round": 0},
                         "a fresh method, even a weaker one, goes before a lookalike")
        self.assertEqual(op.next_qualify(self.rows(), []), {"evolve_file": "ledger/openproblems/evolve-1.jsonl", "round": 7},
                         "equal scores: the earliest row")

    def test_a_row_that_only_reproduces_the_seed_is_marked_told_and_never_the_elite(self):
        asked = []
        seed = {"round": 6, "code": "def predict(*a):\n    return SEED\n", "metrics": M}

        def ask(prompt):
            asked.append(prompt)
            return GOOD
        rows = op.evolve(2, ask, lambda code: dict(M), REF, writer="fake", seed=seed)
        self.assertTrue(rows[0].get("same_as_seed"))
        self.assertIn("same method", asked[1])
        self.assertIs(op.best_or_closest(rows + [seed], REF), seed, "a copy never replaces the seed as the elite")
        self.assertIsNone(op.best(rows, REF))
        for r in rows:
            r.update(code="x = max(1, 1)", reference={"knnr": REF})      # another program, flagged a copy by its numbers
        by_file = {"f": [dict(seed, code="x = 1", reference={"knnr": REF})], "g": rows}
        import hashlib
        receipt = {"source": {"evolve_file": "f", "round": 6}, "code_sha": hashlib.sha256(b"x = 1").hexdigest()}
        self.assertEqual(op.next_qualify(by_file, [receipt]), {"evolve_file": "g", "round": 0},
                         "a flagged lookalike with its own program is still eligible for the held-out sites")
        ci_fail = dict(M, ci={"rmse": [-0.01, 0.01], "mean_pearson_per_cell": [0.03, 0.04]})
        ci_pass = dict(M, ci={"rmse": [-0.03, -0.01], "mean_pearson_per_cell": [0.03, 0.04]})
        rows = op.evolve(1, lambda p: GOOD, lambda code: ci_pass, dict(REF, bootstrap=True), writer="fake",
                         seed=dict(seed, metrics=ci_fail))
        self.assertFalse(rows[0].get("same_as_seed"), "the same numbers but a bootstrap the seed fails: not a copy")

    def test_the_brief_shows_where_the_seed_missed_the_held_out_site_bar(self):
        receipt = {"at": "2026-10-31T19:05:00+00:00", "source": {"evolve_file": "f", "round": 7}, "code_sha": "x",
                   "rows": {"normal": [{"site": 1, "error": None, "cand": {"rmse": 0.9259, "mean_pearson_per_cell": 0.8238},
                                        "ref": {"rmse": 0.9692, "mean_pearson_per_cell": 0.7857}},
                                       {"site": 2, "error": None, "cand": {"rmse": 0.5453, "mean_pearson_per_cell": 0.737},
                                        "ref": {"rmse": 0.5095, "mean_pearson_per_cell": 0.7077}}],
                            "swap": [{"site": 1, "error": None, "cand": {"rmse": 0.30, "mean_pearson_per_cell": 0.77},
                                      "ref": {"rmse": 0.31, "mean_pearson_per_cell": 0.75}}]}}
        receipt["expected_sites"] = {"normal": [1, 2], "swap": [1, 2]}
        receipt["rows"]["swap"].append({"site": 2, "error": None, "cand": {"rmse": 0.30, "mean_pearson_per_cell": 0.77},
                                        "ref": {"rmse": 0.31, "mean_pearson_per_cell": 0.75}})
        note = op.loso_note(receipt)
        self.assertIn("site 2", note)
        self.assertIn("0.5453", note)
        self.assertIn("rmse", note)
        self.assertNotIn("site 1", note, "only the misses are named")
        asked = []
        seed = {"round": 7, "code": "def predict(*a):\n    return SEED\n", "metrics": M}
        op.evolve(1, lambda p: asked.append(p) or "no code", lambda code: {}, REF, writer="fake", seed=seed, seed_note=note)
        self.assertIn("site 2", asked[0])
        self.assertIsNone(op.loso_note(None))
        self.assertIsNone(op.loso_note(dict(receipt, rows={})), "no folds is not a pass")
        self.assertIn("different candidate", op.loso_note(receipt, same_program=False))
        self.assertNotIn("different candidate", op.loso_note(receipt))
        rows = {"f": [{"round": 7, "code": "x = 1", "metrics": M}]}
        self.assertEqual(op.seed_receipt([receipt], {"code": "x = 1  # same program", "metrics": M}, rows), (receipt, True))
        self.assertEqual(op.seed_receipt([receipt], {"code": "x = 2", "metrics": M}, rows), (receipt, False))
        self.assertEqual(op.seed_receipt([receipt], {"code": "x = 2", "metrics": dict(M, rmse=0.5)}, rows), (None, None))
        self.assertIsNone(op.loso_note(dict(receipt, rows={"normal": receipt["rows"]["normal"]})), "a missing direction is not a pass")



class Archive(unittest.TestCase):
    """#598 (2026-11-01): 10-29..10-31 the loop hill-climbed from one seed, 36 asks, 24 distinct behaviors, 6 copies, no
    gain. OpenEvolve and the AlphaEvolve paper keep an archive of diverse elites and sample parents from it. An A/B at
    equal budgets against the single seed; the ledger says which arm each run was."""
    def rows(self):
        def r(n, rmse, pe, code, **kw):
            return {"round": n, "code": code, "metrics": dict(M, rmse=rmse, mean_pearson_per_cell=pe), **kw}
        return [r(0, 0.9259, 0.8238, "best"),                  # passes the bar
                r(1, 0.9259, 0.8238, "best again", same_as_seed=True),
                r(2, 0.9262, 0.8236, "same region as best"),   # same 0.01 cell: not a second slot
                r(3, 0.9400, 0.8200, "another region"),       # passes the bar, other cell
                r(4, 0.9800, 0.7900, "below the bar"),        # below the reference's Pearson
                r(5, 0.9100, 0.8100, "low rmse region"),      # passes, third cell
                {"round": 6, "code": "crash", "error": "x"}]

    def test_the_archive_holds_distinct_behaviors_one_per_region_bar_passers_first(self):
        arch = op.archive(self.rows(), REF, size=3)
        self.assertEqual([a["code"] for a in arch], ["best", "another region", "low rmse region"])
        self.assertEqual([a["code"] for a in op.archive(self.rows(), REF, size=5)],
                         ["best", "another region", "low rmse region", "below the bar"], "a copy of the elite never sits in it")

    def test_the_parent_is_the_best_on_round_0_then_a_seeded_rank_weighted_draw(self):
        arch = op.archive(self.rows(), REF, size=3)
        self.assertIs(op.pick_parent(arch, 0), arch[0])
        picks = [op.pick_parent(arch, i)["code"] for i in range(1, 40)]
        self.assertEqual(picks, [op.pick_parent(arch, i)["code"] for i in range(1, 40)], "seeded: the same draw every time")
        self.assertGreater(picks.count("best"), picks.count("low rmse region"), "rank-weighted")
        self.assertTrue(set(picks) > {"best"}, "other regions are drawn too")

    def test_an_archive_run_shows_the_parent_and_records_it_on_the_row(self):
        asked = []
        arch = op.archive(self.rows(), REF, size=3)
        rows = op.evolve(3, lambda p: asked.append(p) or GOOD, lambda code: {"rmse": 0.99, "mae": 0.7, "mean_pearson_per_cell": 0.70},
                         REF, writer="fake", seed=arch[0], parents=arch)
        self.assertIn("best", asked[0])
        self.assertTrue(all("parent" in r and r["arm"] == "archive" for r in rows))
        empty = op.evolve(1, lambda p: GOOD, lambda code: {"error": "x"}, REF, writer="fake", seed=None, parents=[])
        self.assertEqual((empty[0]["arm"], "parent" in empty[0]), ("archive", False), "the arm is on the row even with nothing to draw")
        self.assertEqual(rows[0]["parent"]["round"], 0)
        self.assertTrue(all("the best so far" in p or "This is" in p for p in asked))

    def test_without_parents_the_single_seed_path_is_unchanged(self):
        asked = []
        seed = {"round": 7, "code": "def predict(*a):\n    return SEED\n", "metrics": M}
        rows = op.evolve(1, lambda p: asked.append(p) or "no code", lambda c: {}, REF, writer="fake", seed=seed)
        self.assertIn("SEED", asked[0])
        self.assertEqual((rows[0]["arm"], "parent" in rows[0]), ("single", False))


class ScreenAgreement(unittest.TestCase):
    """2026-11-03: does a small slice rank candidates as the full validation fit does? Measured before any cheap-score
    stage is built on it."""

    def test_the_slice_labels_are_the_slice_test_cells_and_never_validation(self):
        import tempfile
        from scipy import sparse
        rng = np.random.default_rng(0)
        val, d = Path(tempfile.mkdtemp()), Path(tempfile.mkdtemp()) / "screen"
        b = np.array([f"s{2 + i % 3}d1" for i in range(300)])
        Y = rng.normal(size=(300, 4)).astype(np.float32)
        op.write_inputs(val, sparse.random(300, 7, density=0.3, format="csr", random_state=0), Y,
                        sparse.csr_matrix(np.ones((50, 7))), b, np.array(["s1d1"] * 50))
        y = d.parent / "y.npy"
        op.screen_inputs(val, d, rows=(120, 40), answers=y)
        yt = np.load(y)
        self.assertEqual(yt.shape, (40, 4))
        self.assertTrue(all(any(np.array_equal(r, Y[j]) for j in np.flatnonzero(b == "s4d1")) for r in yt),
                        "each label is a training cell of the slice's test site")
        self.assertFalse((d / "Y_test.npy").exists(), "the labels never sit in the mounted slice")

    def test_candidates_are_distinct_scored_code_newest_first(self):
        import tempfile
        led = Path(tempfile.mkdtemp())
        m = lambda r: {"rmse": r, "mean_pearson_per_cell": 0.8}
        (led / "evolve-1.jsonl").write_text("".join(json.dumps(x) + "\n" for x in [
            {"at": "2026-10-01", "round": 0, "code": "a", "metrics": m(0.95)},
            {"at": "2026-10-02", "round": 1, "code": "b", "error": "crash"},
            {"at": "2026-10-03", "round": 2, "code": "a", "metrics": m(0.95)},      # the same code again
            {"at": "2026-10-04", "round": 3, "code": "c", "metrics": {"rmse": 0.9}}]))   # no Pearson: not comparable
        (led / "evolve-2.jsonl").write_text(json.dumps({"at": "2026-10-05", "round": 0, "code": "d", "metrics": m(0.93)}) + "\n")
        got = op.scored_candidates(led)
        self.assertEqual([(c, r["at"]) for c, r in got], [("d", "2026-10-05"), ("a", "2026-10-03")])

    def test_agreement_is_rank_correlation_and_top_k_kept(self):
        full = [{"rmse": 0.90 + i / 100, "mean_pearson_per_cell": 0.85 - i / 100} for i in range(12)]
        same = [(dict(f), f) for f in full]
        a = op.agreement(same, k=5)
        self.assertEqual((a["n"], a["spearman_rmse"], a["spearman_mean_pearson_per_cell"], a["top5_kept"]), (12, 1.0, 1.0, 5))
        flipped = [({"rmse": -f["rmse"], "mean_pearson_per_cell": -f["mean_pearson_per_cell"]}, f) for f in full]
        b = op.agreement(flipped, k=5)
        self.assertEqual((b["spearman_rmse"], b["top5_kept"]), (-1.0, 0))
        self.assertEqual(op.agreement(same[:4], k=2), {"n": 4, "n_ran": 4, "top2_kept": 2}, "too few for a correlation")
        few = [(None if i >= 4 else dict(f), f) for i, f in enumerate(full)]
        self.assertEqual(op.agreement(few, k=5)["top5_kept"], 4, "Codex f4: retention even when under 5 ran")

    def test_a_full_winner_that_fails_the_slice_counts_as_lost(self):
        """Codex f2: the 10 best by full score all crash on the slice, the other 10 rank perfectly: 0 kept, not 10."""
        full = [{"rmse": 0.90 + i / 100, "mean_pearson_per_cell": 0.85 - i / 100} for i in range(20)]
        pairs = [(None if i < 10 else dict(f), f) for i, f in enumerate(full)]
        a = op.agreement(pairs, k=10)
        self.assertEqual((a["n"], a["n_ran"], a["top10_kept"], a["spearman_rmse"]), (20, 10, 0, 1.0))

    def test_a_constant_ranking_is_null_with_a_reason_not_nan(self):
        full = [{"rmse": 0.90 + i / 100, "mean_pearson_per_cell": 0.8} for i in range(6)]
        a = op.agreement([(dict(f), f) for f in full])
        self.assertIsNone(a["spearman_mean_pearson_per_cell"])
        self.assertIn("constant", a["spearman_mean_pearson_per_cell_why"])
        json.dumps(a, allow_nan=False)


class RoundTiming(unittest.TestCase):
    """C3 (DECISIONS 2026-11-03): each round records every writer ask, and screen, fit and bootstrap seconds per
    direction, so no savings claim rests on ask_s alone (it leaves repairs out)."""

    def test_a_round_with_a_repair_records_every_part(self):
        clock, seen = [], []
        ref = {"rmse": 0.97, "mean_pearson_per_cell": 0.79}

        def screen(code):
            for d in ("normal", "swap"):
                clock.append(("screen", d, 2.0))
            seen.append(code)
            return "normal direction: IndexError" if len(seen) == 1 else None

        def score(code):
            clock.extend([("fit", "normal", 600.0), ("bootstrap", "normal", 10.0), ("fit", "swap", 300.0)])
            return {"rmse": 0.95, "mean_pearson_per_cell": 0.80}
        rows = op.evolve(1, lambda p: GOOD, score, ref, writer="fake", screen=screen, repairs=2, clock=clock)
        t = rows[0]["timing"]
        self.assertEqual((t["calls"], len(t["repair_ask_s"])), (2, 1), "the round ask and one repair")
        self.assertEqual(t["screen_s"], {"normal": 4.0, "swap": 4.0})
        self.assertEqual((t["fit_s"], t["bootstrap_s"]), ({"normal": 600.0, "swap": 300.0}, {"normal": 10.0}))
        self.assertGreaterEqual(t["wall_s"], 0)
        self.assertEqual(rows[0]["repair_asks"], 1)

    def test_entries_before_a_round_are_not_its_own(self):
        clock = [("fit", "normal", 999.0)]                  # a rescore before round 0
        rows = op.evolve(1, lambda p: GOOD, lambda c: {"rmse": 0.95, "mean_pearson_per_cell": 0.80},
                         {"rmse": 0.97, "mean_pearson_per_cell": 0.79}, writer="fake", clock=clock)
        self.assertEqual(rows[0]["timing"]["fit_s"], {})


class ScreenGate(unittest.TestCase):
    """C1 (DECISIONS 2026-11-03): the gate protects the selector's top bar-passers, not the rmse top-k."""

    def ledger(self, n=100):
        import tempfile
        led = Path(tempfile.mkdtemp())
        ref = {"rmse": 1.0, "mean_pearson_per_cell": 0.70}
        rows = [{"at": f"2026-10-{1 + i % 28:02d}T{i % 24:02d}:00", "round": i, "code": f"c{i}",
                 "reference": {op.METHOD: ref},
                 "metrics": {"rmse": 0.99 if i < 40 else 1.01, "mean_pearson_per_cell": 0.80 - i / 1000}} for i in range(n)]
        (led / "evolve-1.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
        sha = lambda c: hashlib.sha256(c.encode()).hexdigest()[:16]
        return led, rows, sha

    def receipt(self, rows, sha, slice_pearson):
        return {"sizes": [[2000, 700]], "rows": [{"code_sha": sha(r["code"]), "at": r["at"], "round": r["round"],
                                                    "full": {m: r["metrics"][m] for m in ("rmse", "mean_pearson_per_cell")},
                                                    "screen": {"2000": s}} for r, s in zip(rows, slice_pearson)]}

    def test_a_slice_that_ranks_like_the_full_fit_passes(self):
        import hashlib  # noqa: F401
        led, rows, sha = self.ledger()
        g = op.screen_gate(self.receipt(rows, sha, [{"mean_pearson_per_cell": r["metrics"]["mean_pearson_per_cell"]} for r in rows]), led)["2000x700"]
        self.assertEqual((g["bar_passers"], g["top_ranks"], g["best_rank"], g["passed"]), (40, list(range(1, 11)), 1, True))

    def test_losing_one_top_bar_passer_past_30_fails_and_a_crash_ranks_last(self):
        led, rows, sha = self.ledger()
        sl = [{"mean_pearson_per_cell": r["metrics"]["mean_pearson_per_cell"]} for r in rows]
        sl[3] = {"error": "IndexError"}                          # the 4th best bar-passer crashes on the slice
        g = op.screen_gate(self.receipt(rows, sha, sl), led)["2000x700"]
        self.assertEqual(g["top_ranks"][3], 100)
        self.assertFalse(g["a"])
        self.assertFalse(g["passed"])

    def test_the_best_must_be_in_the_top_10_and_too_few_runs_fail_c(self):
        led, rows, sha = self.ledger()
        sl = [{"mean_pearson_per_cell": r["metrics"]["mean_pearson_per_cell"]} for r in rows]
        sl[0] = {"mean_pearson_per_cell": 0.7885}                 # the best lands 12th on the slice
        g = op.screen_gate(self.receipt(rows, sha, sl), led)["2000x700"]
        self.assertEqual((g["best_rank"], g["b"], g["a"]), (12, False, True))
        few = [x if i < 80 else {"error": "x"} for i, x in enumerate(sl)]
        self.assertFalse(op.screen_gate(self.receipt(rows, sha, few), led)["2000x700"]["c"], "80 of 100 ran: under 90")


class TimingAndGateFixes(unittest.TestCase):
    """Codex 2026-11-03 round 1 on C3/C1: an unrounded threshold, a timed rescore, API attempts, a complete join."""

    def test_a_rho_that_only_rounds_up_to_the_threshold_fails(self):
        from scipy.stats import spearmanr
        g = ScreenGate()
        led, rows, sha = g.ledger()
        rng = np.random.default_rng(0)
        for _ in range(500):
            noise = rng.normal(scale=0.02, size=len(rows))
            sl = [r["metrics"]["mean_pearson_per_cell"] + e for r, e in zip(rows, noise)]
            rho = float(spearmanr(sl, [r["metrics"]["mean_pearson_per_cell"] for r in rows]).statistic)
            if round(rho, 4) > rho:
                break
        old = op.GATE_RHO
        op.GATE_RHO = round(rho, 4)
        try:
            v = op.screen_gate(g.receipt(rows, sha, [{"mean_pearson_per_cell": x} for x in sl]), led)["2000x700"]
        finally:
            op.GATE_RHO = old
        self.assertEqual(v["spearman_pearson"], round(rho, 4))
        self.assertFalse(v["c"], f"rho {rho!r} is under {round(rho, 4)}")

    def test_a_receipt_row_missing_from_the_ledger_never_passes(self):
        g = ScreenGate()
        led, rows, sha = g.ledger()
        rec = g.receipt(rows, sha, [{"mean_pearson_per_cell": r["metrics"]["mean_pearson_per_cell"]} for r in rows])
        rec["rows"].append({"code_sha": "f" * 16, "screen": {"2000": {"error": "x"}}})
        for x, r in zip(rec["rows"], rows):
            x.update(at=r["at"], round=r["round"], full={m: r["metrics"][m] for m in ("rmse", "mean_pearson_per_cell")})
        v = op.screen_gate(rec, led)["2000x700"]
        self.assertEqual((v["missing"], v["passed"]), (["f" * 16], False))

    def test_the_seed_rescore_row_carries_its_fit_time(self):
        ref = {"rmse": 0.97, "mean_pearson_per_cell": 0.79, "swap": {"rmse": 0.3, "mean_pearson_per_cell": 0.7}}
        prior = [{"round": 3, "code": "c", "at": "2026-10-01", "metrics": {"rmse": 0.95, "mean_pearson_per_cell": 0.80},
                  "reference": {op.METHOD: {"rmse": 0.96, "mean_pearson_per_cell": 0.78}}}]
        clock = [("fit", "normal", 5.0)]                              # earlier work: not the rescore's

        def score(code):
            clock.append(("fit", "normal", 600.0))
            return {"rmse": 0.95, "mean_pearson_per_cell": 0.80, "swap": {"rmse": 0.29, "mean_pearson_per_cell": 0.71}}
        _, rescored = op.timed_seed(prior, ref, score, clock)
        self.assertEqual(rescored["timing"]["fit_s"], {"normal": 600.0})
        self.assertEqual(rescored["timing"]["calls"], 0)

    def test_leanstral_counts_its_dropped_connection_retry(self):
        import http.client, leanstral
        from unittest import mock
        n, ticks = [0], []

        class R:
            def __enter__(self): return self
            def __exit__(self, *a): return False

        def urlopen(req, timeout=None):
            n[0] += 1
            if n[0] == 1:
                raise http.client.RemoteDisconnected("drop")
            return R()
        pacer = type("P", (), {"stop": None, "wait": lambda self: None})()
        with mock.patch.object(leanstral.urllib.request, "urlopen", urlopen), \
             mock.patch.object(leanstral, "read_stream", lambda r: {"usage": {}, "text": "x"}):
            leanstral.call_prompt("k", "p", pacer, on_attempt=lambda: ticks.append(1))
        self.assertEqual(len(ticks), 2)

    def test_router_retries_are_each_an_api_attempt(self):
        from unittest import mock
        import utilities.kumori_api_client as kc
        clock, n = [], [0]

        class Wait(Exception):
            retry_after = 0.01

        def chat(*a, **k):
            n[0] += 1
            if n[0] < 3:
                raise Wait("paced")
            return ("```python\nx\n```", None, None)
        with mock.patch.object(kc, "init", lambda *a, **k: None), mock.patch.object(kc, "llm_chat", chat):
            ask, _ = op.writer_ask("some-lane", clock)
            ask("prompt")
        self.assertEqual(sum(k == "client_call" for k, _, _ in clock), 3)
        self.assertEqual(op.round_timing([1.0], clock, 1.0)["client_calls"], 3)

    def test_a_client_call_that_fails_locally_still_counts_as_a_client_call(self):
        from unittest import mock
        import utilities.kumori_api_client as kc
        clock = []

        def chat(*a, **k):
            raise RuntimeError("not initialized")                  # no request left the machine
        with mock.patch.object(kc, "init", lambda *a, **k: None), mock.patch.object(kc, "llm_chat", chat):
            ask, _ = op.writer_ask("some-lane", clock)
            self.assertIn("error", ask("prompt"))
        self.assertEqual(op.round_timing([1.0], clock, 1.0)["client_calls"], 1, "a client call, labeled as such")

    def test_a_later_rescore_of_the_same_code_cannot_change_the_verdict(self):
        g = ScreenGate()
        led, rows, sha = g.ledger()
        sl = [{"mean_pearson_per_cell": r["metrics"]["mean_pearson_per_cell"]} for r in rows]
        sl[0] = {"mean_pearson_per_cell": 0.70}                       # the best bar-passer ranks last on the slice
        rec = g.receipt(rows, sha, sl)
        for x, r in zip(rec["rows"], rows):
            x.update(at=r["at"], round=r["round"], full={m: r["metrics"][m] for m in ("rmse", "mean_pearson_per_cell")})
        before = op.screen_gate(rec, led)["2000x700"]
        later = dict(rows[0], at="2026-12-01T00:00", round=-1, metrics={"rmse": 1.5, "mean_pearson_per_cell": 0.1})
        with open(led / "evolve-1.jsonl", "a") as f:
            f.write(json.dumps(later) + "\n")
        after = op.screen_gate(rec, led)["2000x700"]
        self.assertEqual((before["passed"], before["best_rank"]), (False, 100))
        self.assertEqual((after["passed"], after["best_rank"], after["missing"]), (False, 100, []))


if __name__ == "__main__":
    unittest.main()
