"""tools/openproblems.py: the upstream script runs with only its VIASH block swapped, the published score is read
from the maintainers' own results file, and the 1% gate fails a wrong run (the canary). No network, no data."""
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


if __name__ == "__main__":
    unittest.main()
