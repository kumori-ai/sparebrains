"""The goal closer (tools/goal_closer.py, task #461): which goals, restatements flagged, and a proved goal
spliced back into its sketch. No Lean here: a stand-in judge."""
import sys
import unittest
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


if __name__ == "__main__":
    unittest.main()
