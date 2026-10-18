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
