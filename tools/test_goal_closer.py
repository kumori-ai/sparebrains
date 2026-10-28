"""The goal closer (tools/goal_closer.py, task #461): which goals, restatements flagged, and a proved goal
spliced back into its sketch. No Lean here: a stand-in judge."""
import sys
import unittest
from unittest import mock
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import goal_closer as gc

TARGET = """import Mathlib

theorem t (x y : ℤ) (h₀ : y ^ 2 + 3 * x = 7) :
    3 * x = 7 - y ^ 2 := by
  sorry
"""
RESTATED = ("theorem sb_goal (x y : ℤ) (h₀ : y ^ (2 : ℕ) + (3 : ℤ) * x = (7 : ℤ)) :\n"
            "  (3 : ℤ) * x = (7 : ℤ) - y ^ (2 : ℕ) := by")
STEP = "theorem sb_goal (x y : ℤ) (h₀ : y ^ 2 + 3 * x = 7) : y ^ 2 ≤ 7 + 3 * x := by"
SKETCH = "\n  have h : y ^ 2 ≤ 7 + 3 * x := by\n    sorry\n  omega"


def row(target, sketch, goals, tset="s"):
    return {"target_set": tset, "target": target, "tools": {"sketch": sketch, "subgoals": str({"goals": goals})}}


class Collect(unittest.TestCase):
    def test_a_goal_with_the_theorems_conclusion_restates_it(self):
        self.assertTrue(gc.restates(RESTATED, TARGET))
        self.assertFalse(gc.restates(STEP, TARGET))

    def test_one_step_open_goals_deduplicated_real_steps_first(self):
        rows = [row("t", "\n  sorry", [RESTATED]), row("t", SKETCH, [STEP]), row("t", SKETCH + "\n", [STEP + "  "]),
                row("t", SKETCH, [STEP, RESTATED]),                  # two steps open: not a one-step goal
                row("solved", SKETCH, [STEP])]                       # not open
        goals = gc.collect(rows, {("s", "t")}, lambda s, t: TARGET)
        self.assertEqual([g["restates"] for g in goals], [False, True])
        self.assertEqual(len(goals[0]["sketches"]), 2)

    def test_the_goal_file_carries_the_targets_header(self):
        f = gc.goal_file(TARGET, STEP)
        self.assertTrue(f.startswith("import Mathlib\n"))
        self.assertIn(STEP + "\n  sorry", f)


class Check(unittest.TestCase):
    def test_only_a_goal_lean_can_read_alone_is_kept(self):
        goals = [{"target_set": "s", "target": "t", "goal": STEP}, {"target_set": "s", "target": "t", "goal": "bad"}]
        judge = lambda text: {"verdict": "wellformed" if STEP in text else "reject"}
        self.assertEqual([g["file_ok"] for g in gc.check(goals, lambda s, t: TARGET, judge)], [True, False])


TYPED = "theorem sb_goal (x y : ℤ) (h₀ : y ^ (2 : ℕ) + (3 : ℤ) * x = (7 : ℤ)) : y ^ (2 : ℕ) ≤ (7 : ℤ) + (3 : ℤ) * x := by"


class Retype(unittest.TestCase):
    """Goals from rows before 2026-10-09 were printed without numeric types: extracted again from their sketches."""
    def extract(self, results):
        it = iter(results)
        return mock.patch.object(gc.subgoals, "automate_and_goals", side_effect=lambda text, top, run: next(it))

    def test_each_sketch_gets_its_goal_again_and_a_closed_hole_is_flagged(self):
        g = {"sha": "old", "target_set": "s", "target": "t", "goal": STEP, "sketches": [SKETCH, SKETCH + "\n"]}
        judge = lambda text: {"verdict": "wellformed"}
        with self.extract([("", {5: TYPED}, {"holes": 1, "open": 1}), ("", {}, {"holes": 1, "open": 0})]):
            rows = gc.retype([g], lambda s, t: TARGET, None, judge, slice_=(0, 1), jobs=1)
        self.assertEqual([(r["sketch"], r["goal"], r["file_ok"], r["closed_now"]) for r in rows],
                         [(0, TYPED, True, False), (1, None, False, True)])
        self.assertEqual(rows[0]["sha"], gc.goal_sha(TYPED))
        self.assertFalse(rows[0]["same"])                    # the canary: a typed goal comes back identical

    def test_the_queue_is_rebuilt_from_the_rows_grouped_by_the_new_goal(self):
        rows = [{"old": "a", "sketch": 0, "target_set": "s", "target": "t", "goal": TYPED, "file_ok": True},
                {"old": "b", "sketch": 0, "target_set": "s", "target": "t", "goal": TYPED, "file_ok": True},
                {"old": "b", "sketch": 1, "target_set": "s", "target": "t", "goal": None, "file_ok": False},
                {"old": "c", "sketch": 0, "target_set": "s", "target": "t", "goal": RESTATED, "file_ok": True}]
        queue = [{"sha": "a", "sketches": [SKETCH]}, {"sha": "b", "sketches": [SKETCH + " ", "\n  sorry"]},
                 {"sha": "c", "sketches": ["\n  sorry"]}]
        q = gc.requeue(rows, queue, lambda s, t: TARGET)
        self.assertEqual([(g["goal"], len(g["sketches"]), g["restates"]) for g in q],
                         [(TYPED, 2, False), (RESTATED, 1, True)])
        self.assertTrue(all(g["file_ok"] for g in q))


class Close(unittest.TestCase):
    def test_a_proof_lands_in_the_one_hole(self):
        cand = gc.splice(TARGET, SKETCH, "nlinarith [sq_nonneg y]\n")
        self.assertIn("  have h : y ^ 2 ≤ 7 + 3 * x := by\n    nlinarith [sq_nonneg y]\n  omega", cand)
        self.assertNotIn("sorry", cand[len(gc.prefix_of(TARGET)):])

    def test_goal_then_problem_and_where_it_stopped(self):
        seen = []
        judge = lambda text: (seen.append(text), {"verdict": "accept" if "nlinarith" in text else "reject"})[1]
        g = {"goal": STEP, "sketches": [SKETCH]}
        self.assertEqual(gc.close(g, TARGET, "  rfl\n", judge)["stage"], "goal")
        ok = gc.close(g, TARGET, "  nlinarith [sq_nonneg y]\n", judge)
        self.assertEqual((ok["verdict"], ok["stage"]), ("accept", "problem"))
        self.assertTrue(seen[-1].startswith("import Mathlib") and "theorem t" in seen[-1])

    def test_templates_build_hints_from_the_goals_own_variables(self):
        g = "theorem sb_goal (x y : ℝ) (n : ℕ) (h₀ : x + y = 1) (h₁ : n ≤ 5) : x * y ≤ 1 / 4 := by"
        self.assertEqual(gc.goal_vars(g), {"ℝ": ["x", "y"], "ℕ": ["n"]})
        self.assertEqual(gc.expand("@nlinarith-sq", g),
                         "nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]")
        self.assertEqual(gc.expand("@interval-cases", g), "interval_cases n <;> omega")
        self.assertEqual(gc.expand("grind", g), "grind")
        bare = "theorem sb_goal : (1 / 2 : ℚ) + (1 / 3 : ℚ) = (5 / 6 : ℚ) := by"
        self.assertIsNone(gc.expand("@nlinarith-sq", bare))       # nothing to build from: not tried
        self.assertIsNone(gc.expand("@interval-cases", bare))

    def test_a_template_row_names_the_template_and_the_tactics_it_became(self):
        g = {"sha": "a", "target_set": "s", "target": "t", "goal": "theorem sb_goal (y : ℝ) : y = y := by",
             "sketches": [SKETCH]}
        run_lean = lambda text: ("", 1.0)
        rows, cands = gc.sweep([g], ["@nlinarith-sq", "@interval-cases"], lambda s, t: TARGET, run_lean,
                               lambda text: {"verdict": "reject"}, lambda g: "open", 1)
        self.assertEqual([(r["recipe"], r.get("tactics")) for r in rows],
                         [("@nlinarith-sq", "nlinarith [sq_nonneg y]")])    # no ℕ variable: interval-cases skipped

    def test_recipes_share_one_file_and_errors_are_placed_by_line(self):
        text, starts = gc.recipe_file(TARGET, STEP, ["grind", "field_simp; ring_nf"])
        self.assertEqual([n for n, _ in starts], ["sb_goal_r0", "sb_goal_r1"])
        lines = text.split("\n")
        self.assertTrue(lines[starts[1][1] - 1].startswith("theorem sb_goal_r1"))
        self.assertIn("  field_simp\n  ring_nf\n", text)
        r1 = starts[1][1]
        out = f"proof.lean:{r1 + 1}:2: error: ring_nf failed\nproof.lean:{starts[0][1]}:8: warning: unused variable"
        self.assertEqual(gc.recipes_passing(out, starts, len(lines)), [0])
        sorry = f"proof.lean:{starts[0][1]}:8: warning: declaration uses 'sorry'"
        self.assertEqual(gc.recipes_passing(sorry, starts, len(lines)), [1])
        self.assertEqual(gc.recipes_passing("timeout after 180s", starts, len(lines)), [])

    def test_the_sweep_judges_only_filter_passes_and_keeps_no_proof_text_in_rows(self):
        judged = []
        judge = lambda text: (judged.append(text), {"verdict": "accept" if "grind" in text else "reject"})[1]
        def run_lean(text):                              # recipe 1 errors, recipe 0 is clean
            _, starts = gc.recipe_file(TARGET, STEP, ["grind", "omega"])
            return f"proof.lean:{starts[1][1] + 1}:2: error: omega could not prove the goal", 3.0
        g = {"sha": "a", "target_set": "s", "target": "t", "goal": STEP, "sketches": [SKETCH], "status": "solved"}
        rows, cands = gc.sweep([g], ["grind", "omega"], lambda s, t: TARGET, run_lean, judge, lambda g: g["status"], 1)
        self.assertEqual([(r["recipe"], r["outcome"], r["stage"], r["status"]) for r in rows],
                         [("grind", "solved", "problem", "solved"), ("omega", "failed", "goal", "solved")])
        self.assertTrue(all("verdict" not in r and "ts" not in r for r in rows))   # never counted as a try
        self.assertTrue(all("candidate" not in r for r in rows))
        self.assertIn(("a", "grind"), cands)
        self.assertEqual(len(judged), 2)       # grind's goal and its splice; the filtered recipe never reaches the judge

    def test_a_sweep_solve_is_recorded_as_a_goal_closer_try_by_the_recipe_lane(self):
        import prover
        rec = type("R", (), {"rows": [], "proofs": [],
                             "__call__": lambda self, row, *a: self.rows.append(row),
                             "verified": lambda self, s, t, c: self.proofs.append((t, c))})()
        judge = lambda text: {"verdict": "accept" if "grind" in text else "reject"}
        g = {"sha": "a", "target_set": "minif2f/test", "target": "t", "goal": "theorem sb_goal (y : ℕ) : y = y := by",
             "sketches": [SKETCH]}
        with mock.patch.object(prover, "prover_rows", return_value=[]), \
             mock.patch.object(Path, "read_text", return_value=TARGET):
            stats = gc.publish_solves([("a", "grind")], {"a": g}, "tactics-0of1", rec, judge)
        self.assertEqual(stats["solved"], 1)
        (row,) = rec.rows
        self.assertEqual((row["try_mode"], row["backend"], row["model"], row["verdict"]),
                         ("goal-closer", "lean-tactic-recipe", "recipe: grind", "accept"))
        self.assertIn("grind", rec.proofs[0][1])

    def test_a_tactic_is_tried_on_readable_goals_only_and_closes_whole_problems(self):
        judge = lambda text: {"verdict": "accept" if "grind" in text else "reject"}
        goals = [{"sha": "a", "target_set": "s", "target": "t", "restates": False, "goal": STEP,
                  "sketches": [SKETCH], "file_ok": True},
                 {"sha": "b", "target_set": "s", "target": "u", "restates": False, "goal": STEP,
                  "sketches": [SKETCH], "file_ok": False}]
        rows = gc.try_tactic(goals, "grind", lambda s, t: TARGET, judge, jobs=2)
        self.assertEqual([(r["sha"], r["verdict"], r["stage"]) for r in rows], [("a", "accept", "problem")])
        self.assertIn("grind", rows[0]["candidate"])
        miss = gc.try_tactic(goals, "omega", lambda s, t: TARGET, judge, jobs=1)
        self.assertEqual([(r["verdict"], r["stage"]) for r in miss], [("reject", "goal")])



class Batches(unittest.TestCase):
    """Goal batches through the prover lane (tools/prover.py, task #461)."""

    def test_only_goals_lean_can_read_become_batch_problems(self):
        goals = [{"sha": "a1", "target_set": "s", "target": "t", "goal": STEP, "file_ok": True},
                 {"sha": "b2", "target_set": "s", "target": "t", "goal": "bad", "file_ok": False}]
        q = gc.queue(goals, lambda s, t: TARGET, 8)
        self.assertEqual([(p["goal"], p["n"]) for p in q], [("a1", 8)])
        self.assertIn("theorem sb_goal", q[0]["statement"])

    def test_a_tried_goal_or_a_closed_problem_is_not_owed(self):
        import prover
        q = [{"target_set": "s", "target": "t", "goal": "a1"}, {"target_set": "s", "target": "t", "goal": "b2"},
             {"target_set": "s", "target": "done", "goal": "c3"}]
        rows = [{"try_mode": "goal-closer", "goal": "a1", "target_set": "s", "target": "t"}]
        self.assertEqual([w["goal"] for w in prover.goal_work(q, {("s", "t")}, rows)], ["b2"])

    def test_a_goal_answer_is_judged_alone_then_spliced_and_recorded(self):
        import prover
        rec = []

        class Rec:
            def __call__(self, row, *a):
                rec.append(row)

            def verified(self, *a):
                rec.append(("verified",) + a[:2])
        goal = {"sha": "a1", "goal": STEP, "sketches": [SKETCH]}
        answer = {"batch": "goals-x", "target_set": "s", "target": "t", "sample": 0, "goal": "a1",
                  "text": "```lean4\n" + STEP + "\n  nlinarith [sq_nonneg y]\n```"}
        judge = lambda text: {"verdict": "accept" if "nlinarith" in text else "reject"}
        with mock.patch.object(prover, "ROOT", FakeRoot()):
            stats = prover.judge_goals([answer], [], {"a1": goal}, judge_text=judge, record=Rec(), run_id="r")
        self.assertEqual(stats.get("solved"), 1)
        self.assertEqual((rec[0]["try_mode"], rec[0]["stage"], rec[0]["verdict"], rec[0]["goal"]),
                         ("goal-closer", "problem", "accept", "a1"))
        self.assertEqual(rec[1], ("verified", "s", "t"))


class FakeRoot:
    """ROOT / "targets" / set / f"{name}.lean" reads TARGET."""
    def __truediv__(self, other):
        return self

    def read_text(self):
        return TARGET


if __name__ == "__main__":
    unittest.main()


class UnsweptTests(unittest.TestCase):
    """The scheduled sweep (2026-10-28) takes only goals a recipe has never been tried on, so a weekly run is new
    work, never the same Lean runs again (DECISIONS 2026-10-19: real project work only)."""
    GOALS = [{"sha": "a", "target_set": "s", "target": "t1", "goal": "g"},
             {"sha": "b", "target_set": "s", "target": "t2", "goal": "g"},
             {"sha": "c", "target_set": "s", "target": "t3", "goal": "g"}]
    ROWS = [{"sha": "a", "recipe": "grind", "outcome": "failed"}, {"sha": "a", "recipe": "bound", "outcome": "failed"},
            {"sha": "b", "recipe": "grind", "outcome": "failed"}]

    def test_a_goal_every_recipe_was_tried_on_is_left_out(self):
        self.assertEqual([g["sha"] for g in gc.unswept(self.GOALS, self.ROWS, ["grind", "bound"])], ["b", "c"])

    def test_a_new_recipe_makes_every_goal_new_again(self):
        self.assertEqual([g["sha"] for g in gc.unswept(self.GOALS, self.ROWS, ["grind", "omega"])], ["a", "b", "c"])

    def test_a_templated_recipe_with_no_row_does_not_make_a_goal_new(self):
        self.assertEqual([g["sha"] for g in gc.unswept(self.GOALS, self.ROWS, ["grind", "bound", "@interval-cases"])], ["b", "c"])

    def test_no_rows_means_every_goal(self):
        self.assertEqual(len(gc.unswept(self.GOALS, [], ["grind"])), 3)
