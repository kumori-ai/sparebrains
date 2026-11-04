"""tools/openproblems_registry.py: C2 R5's manifest, dispatch gate, freeze and read (DECISIONS 2026-11-04).
No network, no data."""
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).parent))
import openproblems as op
import openproblems_registry as reg

REF = {"rmse": 0.97, "mean_pearson_per_cell": 0.79, "swap": {"rmse": 0.31, "mean_pearson_per_cell": 0.77}}
GOOD = {"rmse": 0.93, "mean_pearson_per_cell": 0.82, "swap": {"rmse": 0.30, "mean_pearson_per_cell": 0.78}}


class Registry(unittest.TestCase):
    def setUp(self):
        self.top = Path(tempfile.mkdtemp())
        self.root = self.top / "ledger"
        self.exp = self.root / "openproblems" / "experiments"
        self.exp.mkdir(parents=True)
        rows = [{"at": f"2026-11-0{1 + i // 5}T00:00:0{i % 5}+00:00", "round": i, "code": f"def predict(): {i}",
                 "reference": {op.METHOD: REF}, "metrics": GOOD} for i in range(9)]
        rows.append({"at": "2026-11-01T01:00:00+00:00", "round": 20, "code": "def predict(): 0", "reference": {op.METHOD: REF},
                     "metrics": GOOD})                                                 # same code as round 0: one seed
        rows.append({"at": "2026-11-01T02:00:00+00:00", "round": 21, "code": "bad", "reference": {op.METHOD: REF},
                     "metrics": {"rmse": 1.2, "mean_pearson_per_cell": 0.5}})          # fails the bar
        rows.append({"at": "2026-11-09T00:00:00+00:00", "round": 22, "code": "late", "reference": {op.METHOD: REF},
                     "metrics": GOOD})                                                 # after seed_upto
        (self.root / "openproblems" / "evolve-1.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
        self.shake("l", "complete")
        self.man = reg.make_manifest(self.root, "c2", "l", "2026-11-05T00:00:00+00:00", "s1", "E" * 40, "C" * 40)
        self.reg = self.exp / "c2"
        self.reg.mkdir()
        (self.reg / "manifest.json").write_text(json.dumps(self.man))
        self.run = 100

    def shake(self, lane, final, name="9"):
        rows = [{"experiment": "shakedown-x", "frozen": {"lane": lane}, "round": 0},
                {"experiment": "shakedown-x", "frozen": {"lane": lane}, "round": None, "terminal": {"final": final}}]
        (self.exp / f"evolve-{name}.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))

    def dispatch(self, pair, arm, attempt=1, end="complete"):
        """The gate, then the arm's rows as its job would publish them (end None: the job died with no file)."""
        self.run += 1
        reg.gate(self.reg, pair, arm, attempt, self.run, self.reg / "dispatches.jsonl")
        if end:
            rows = [{"round": 0, "pair": {"id": pair}}, {"round": None, "terminal": {"final": end}}]
            reg.arm_file(self.reg, self.run).write_text("".join(json.dumps(r) + "\n" for r in rows))
        return self.run

    def pair(self, i):
        return self.man["pairs"][i]

    def both(self, p, attempt=1, ends=("complete", "complete")):
        second = "off" if p["first"] == "on" else "on"
        return {p["first"]: self.dispatch(p["id"], p["first"], attempt, ends[0]),
                second: self.dispatch(p["id"], second, attempt, ends[1])}

    def test_the_manifest_has_six_distinct_bar_passing_seeds_and_three_of_each_order(self):
        pairs = self.man["pairs"]
        self.assertEqual([p["id"] for p in pairs], [f"p{i}" for i in range(1, 7)])
        self.assertEqual(sorted(p["first"] for p in pairs), ["off"] * 3 + ["on"] * 3)
        self.assertEqual(len({p["seed_from"]["code_sha"] for p in pairs}), 6)
        self.assertEqual(self.man["pool"], 9, "the duplicate code, the bar failure and the late row are not seeds")
        for p in pairs:
            _, sf = op.seed_source(self.root, f"{p['seed_from']['file']}:{p['seed_from']['round']}")
            self.assertEqual(sf, p["seed_from"], "each seed resolves exactly as an arm will resolve it")
        again = reg.make_manifest(self.root, "c2", "l", "2026-11-05T00:00:00+00:00", "s1", "E" * 40, "C" * 40)
        self.assertEqual(again["pairs"], pairs, "the fixed seed reproduces the draw and the order")
        other = reg.make_manifest(self.root, "c2", "l", "2026-11-05T00:00:00+00:00", "s2", "E" * 40, "C" * 40)
        self.assertNotEqual(other["pairs"], pairs)

    def test_r6_a_lane_needs_a_completed_shakedown(self):
        self.shake("m", "incomplete", name="8")
        with self.assertRaises(SystemExit):
            reg.make_manifest(self.root, "c2", "m", "2026-11-05T00:00:00+00:00", "s1", "E" * 40, "C" * 40)

    def test_the_inputs_digest_moves_with_a_late_pre_cutoff_row_and_not_with_a_post_cutoff_one(self):
        """Codex 20261104T085109300085Z f2: a row stamped before seed_upto and published later changes the archive."""
        d0 = self.man["inputs_digest"]
        f = self.root / "openproblems" / "evolve-2.jsonl"
        f.write_text(json.dumps({"at": "2026-11-10T00:00:00+00:00", "round": 0, "code": "x"}) + "\n")
        self.assertEqual(reg.inputs_digest(reg.prior_rows(self.root, self.man["seed_upto"])), d0)
        f.write_text(json.dumps({"at": "2026-11-04T23:00:00+00:00", "round": 0, "code": "x"}) + "\n")
        self.assertNotEqual(reg.inputs_digest(reg.prior_rows(self.root, self.man["seed_upto"])), d0)

    def test_the_first_arm_goes_first_and_no_arm_runs_twice(self):
        p = self.pair(0)
        second = "off" if p["first"] == "on" else "on"
        self.assertIn("first", reg.why_not(self.reg, p["id"], second, 1))
        self.dispatch(p["id"], p["first"])
        self.assertIn("already dispatched", reg.why_not(self.reg, p["id"], p["first"], 1))
        self.assertIsNone(reg.why_not(self.reg, p["id"], second, 1))
        self.assertIn("not a registered arm", reg.why_not(self.reg, "p7", "on", 1))
        self.assertIn("not a registered arm", reg.why_not(self.reg, p["id"], "on", 3))
        with self.assertRaises(SystemExit):
            reg.gate(self.reg, p["id"], p["first"], 1, 999, self.reg / "dispatches.jsonl")

    def test_attempt_two_only_after_an_invalid_attempt_one(self):
        p, q = self.pair(0), self.pair(1)
        self.assertIn("attempt 1 INVALID", reg.why_not(self.reg, p["id"], p["first"], 2))
        self.both(p)
        self.assertIn("complete", reg.why_not(self.reg, p["id"], p["first"], 2), "a complete pair is never rerun")
        self.both(q, ends=("complete", None))                     # the second arm's job died before publishing
        self.assertIsNone(reg.why_not(self.reg, q["id"], q["first"], 2), "a missing file is an incomplete arm")

    def test_a_truncated_or_incomplete_terminal_makes_the_attempt_invalid(self):
        p = self.pair(0)
        runs = self.both(p, ends=("complete", "incomplete"))
        self.assertEqual(reg.attempt_state(self.reg, reg.load(self.reg)[1], p["id"], 1), "invalid")
        f = reg.arm_file(self.reg, runs[p["first"]])
        lines = f.read_text().splitlines()
        f.write_text("\n".join(lines[::-1]) + "\n")            # the terminal row is not the last
        self.assertFalse(reg.terminal_complete(reg.rows_of(f)))

    def test_evolve_checks_its_own_dispatch_record_and_the_manifest(self):
        p = self.pair(0)
        run = self.dispatch(p["id"], p["first"], end=None)
        got = reg.check_dispatch(self.reg, p["id"], p["first"], 1, run)
        self.assertEqual(got["settings"], {"lane": "l", "seed_upto": self.man["seed_upto"], "max_asks": 24, "rounds": 12,
                                           **reg.ARMS[p["first"]]})
        with self.assertRaises(SystemExit):
            reg.check_dispatch(self.reg, p["id"], p["first"], 1, run + 1)       # another run's record
        with self.assertRaises(SystemExit):
            reg.check_dispatch(self.reg, p["id"], "on" if p["first"] == "off" else "off", 1, run)
        (self.reg / "manifest.json").write_text(json.dumps(dict(self.man, lane="other")))
        with self.assertRaises(SystemExit):
            reg.check_dispatch(self.reg, p["id"], p["first"], 1, run)

    def settle(self):
        """p1 valid on attempt 1; p2 invalid then valid; p3 invalid twice (FAILED); p4-p6 valid."""
        ps = self.man["pairs"]
        self.both(ps[0])
        self.both(ps[1], ends=("incomplete", "complete")); self.both(ps[1], attempt=2)
        self.both(ps[2], ends=(None, "complete")); self.both(ps[2], attempt=2, ends=("complete", "incomplete"))
        for p in ps[3:]:
            self.both(p)

    def test_the_freeze_waits_for_every_pair_then_picks_the_first_valid_run_once(self):
        ps = self.man["pairs"]
        self.both(ps[0])
        with self.assertRaises(SystemExit):
            reg.freeze(self.reg)                                  # p2..p6 not settled
        self.both(ps[1], ends=("incomplete", "complete"))
        for p in ps[2:]:
            self.both(p)
        with self.assertRaises(SystemExit):
            reg.freeze(self.reg)                                  # p2 attempt 1 INVALID and its rerun not run
        self.both(ps[1], attempt=2)
        sel = reg.freeze(self.reg)
        self.assertEqual([(x["pair"], x["attempt"], x["status"]) for x in sel["pairs"]],
                         [("p1", 1, "valid"), ("p2", 2, "valid")] + [(f"p{i}", 1, "valid") for i in range(3, 7)])
        self.assertTrue(all(v.startswith("ledger/openproblems/experiments/evolve-") for x in sel["pairs"] for v in x["files"].values()))
        with self.assertRaises(SystemExit):
            reg.freeze(self.reg)
        self.assertIn("frozen", reg.why_not(self.reg, "p1", "on", 2))

    def receipts(self, sel, outcome):
        out = []
        for x in sel["pairs"]:
            for arm, f in x["files"].items():
                out.append({"experiment": "c2", "seed_from": {"pair": x["pair"]}, "arm": reg.ARMS[arm]["parents"],
                            "evaluator": "E", "frozen": {"lane": "l", **reg.ARMS[arm]}, "evolve_file": f,
                            "outcome": outcome(x["pair"], arm)})
        return out

    def test_the_read_counts_a_failed_pair_as_a_non_win_and_claims_only_six_of_six(self):
        self.settle()
        sel = reg.freeze(self.reg)
        self.assertEqual([x["status"] for x in sel["pairs"]].count("FAILED"), 1)
        v = reg.read(self.reg, self.receipts(sel, lambda p, a: 0.1 if a == "on" else 0.0))
        self.assertEqual((v["wins"], v["failed"], v["n"], v["read"]), (5, ["p3"], 6, "no claim"))
        self.assertIn("INCOMPLETE", reg.read(self.reg, self.receipts(sel, lambda p, a: 0.1)[:-1])["read"])

    def test_six_valid_wins_is_the_only_lift(self):
        for p in self.man["pairs"]:
            self.both(p)
        sel = reg.freeze(self.reg)
        v = reg.read(self.reg, self.receipts(sel, lambda p, a: 0.1 if a == "on" else 0.0))
        self.assertEqual((v["wins"], v["p"], v["read"]), (6, 0.0156, "tools lift"))
        stray = self.receipts(sel, lambda p, a: 0.1 if a == "on" else 0.0)
        stray.append(dict(stray[0], evolve_file="ledger/openproblems/experiments/evolve-1.jsonl", outcome=-5))
        self.assertEqual(reg.read(self.reg, stray)["read"], "tools lift", "a run not selected is never read")
        dup = self.receipts(sel, lambda p, a: 0.1 if a == "on" else 0.0)
        dup.append(dict(dup[0], outcome=0.5))
        self.assertIn("INCOMPLETE", reg.read(self.reg, dup)["read"], "two disagreeing receipts for one arm")

    def test_the_evolve_cli_refuses_before_any_ask(self):
        """No record for this run, another evaluator, another ledger commit, or moved inputs: exit before writer_ask."""
        p = self.pair(0)
        run = self.dispatch(p["id"], p["first"], end=None)
        work = self.top / "work"
        for d in ("answers", "answers-swap"):
            (work / d).mkdir(parents=True)
            (work / d / "ref.json").write_text(json.dumps(REF))
        argv = lambda rid: ["openproblems.py", "evolve", "--work", str(work), "--out", str(self.exp / "evolve-x.jsonl"),
                            "--pair", p["id"], "--arm", p["first"], "--attempt", "1", "--registry", str(self.reg),
                            "--ledger-root", str(self.root), "--run-id", str(rid)]
        heads = {"eval": "E" * 40, "ledger": "C" * 40}
        head = lambda path: heads["ledger"] if Path(path) == self.top else heads["eval"]
        def boom(*a, **k):
            raise AssertionError("reached the writer")
        def run_main(rid):
            with mock.patch.object(sys, "argv", argv(rid)), mock.patch.object(op, "git_head", head), \
                 mock.patch.object(op, "writer_ask", boom):
                op.main()
        with self.assertRaises(AssertionError):
            run_main(run)                                       # the canary: every check passes, the writer is reached
        for change in ("rid", "eval", "ledger", "inputs"):
            heads.update(eval="E" * 40, ledger="C" * 40)
            rid = run + 1 if change == "rid" else run
            if change in heads:
                heads[change] = "F" * 40
            if change == "inputs":
                (self.root / "openproblems" / "evolve-3.jsonl").write_text(json.dumps({"at": "2026-11-01T00:00:00+00:00"}) + "\n")
            with self.assertRaises(SystemExit, msg=change):
                run_main(rid)


class Barrier(unittest.TestCase):
    """Codex 20261104T085109300085Z f1: no held-out or test measurement of an experiment arm outside outcome."""

    def test_qualify_final_and_reserve_refuse_an_experiment_file(self):
        d = Path(tempfile.mkdtemp()) / "ledger" / "openproblems" / "experiments"
        d.mkdir(parents=True)
        f = d / "evolve-5.jsonl"
        f.write_text(json.dumps({"round": 0, "code": "c", "metrics": GOOD}) + "\n")
        for fn in (op.candidate_row, op.candidate_from):
            with self.assertRaises(SystemExit):
                fn(str(f), 0)
        main_f = d.parent / "evolve-5.jsonl"
        main_f.write_text(f.read_text())
        self.assertEqual(op.candidate_from(str(main_f), 0), "c", "the canary: a main-ledger file still loads")

    def test_outcome_of_a_registered_arm_needs_the_freeze_and_its_file_in_it(self):
        top = Path(tempfile.mkdtemp())
        exp = top / "ledger" / "openproblems" / "experiments"
        (exp / "c2").mkdir(parents=True)
        f = exp / "evolve-7.jsonl"
        f.write_text(json.dumps({"experiment": "c2", "pair": {"id": "p1", "arm": "on", "attempt": 1}, "round": 0}) + "\n"
                     + json.dumps({"experiment": "c2", "pair": {"id": "p1", "arm": "on", "attempt": 1}, "round": None,
                                   "terminal": {"final": "complete"}}) + "\n")
        calls = []
        with self.assertRaises(SystemExit):
            op.outcome(top / "ledger", "ledger/openproblems/experiments/evolve-7.jsonl", top / "o.json", "A" * 40,
                       lambda c: calls.append(c))
        (exp / "c2" / "selection.json").write_text(json.dumps({"pairs": [{"pair": "p1", "status": "valid", "attempt": 1,
                                                                          "files": {"on": "ledger/openproblems/experiments/evolve-8.jsonl"}}]}))
        with self.assertRaises(SystemExit):
            op.outcome(top / "ledger", "ledger/openproblems/experiments/evolve-7.jsonl", top / "o.json", "A" * 40,
                       lambda c: calls.append(c))
        self.assertEqual(calls, [])


class FreezeWorkflow(unittest.TestCase):
    """Codex 20261104T090419176107Z f1: the freeze workflow's own shell, as GitHub runs it (bash -e, no pipefail),
    fails on an unsettled experiment and never reaches publication; a settled one writes selection.json."""

    def steps(self):
        import yaml
        wf = yaml.safe_load((Path(__file__).parent.parent / ".github/workflows/openproblems_pairs.yml").read_text())
        return {s.get("name"): s["run"] for s in wf["jobs"]["freeze"]["steps"] if "run" in s}

    def run_step(self, script, cwd):
        import subprocess
        script = script.replace("${{ inputs.experiment }}", "c2")
        return subprocess.run(["bash", "-e", "-c", script], cwd=cwd, capture_output=True, text=True,
                              env={"PATH": "/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin", "RUNNER_TEMP": str(cwd)})

    def test_an_unsettled_freeze_fails_and_a_settled_one_writes_the_selection(self):
        t = Registry("setUp")
        t.setUp()
        (t.top / "tools").symlink_to(Path(__file__).parent)
        steps = self.steps()
        r = self.run_step(steps["freeze the pairs"], t.top)
        self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
        pub = self.run_step(steps["publish selection.json"].split("git config")[0], t.top)
        self.assertNotEqual(pub.returncode, 0, "publication refuses without selection.json")
        for p in t.man["pairs"]:
            t.both(p)
        r = self.run_step(steps["freeze the pairs"], t.top)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertTrue((t.reg / "selection.json").exists())
        self.assertEqual(self.run_step(steps["publish selection.json"].split("git config")[0], t.top).returncode, 0)


if __name__ == "__main__":
    unittest.main()
