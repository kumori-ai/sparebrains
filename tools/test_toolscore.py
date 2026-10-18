"""The tool scoreboard (tools/toolscore.py, task #463): which tools a chain run used, which arms are re-run, and
that leaving a tool out really leaves it out. No Lean here: a stand-in judge."""
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).parent))
import fixer
import subgoals
import toolscore

PREFIX = "theorem t : 1 = 1 := by"


class FakeLean:
    """Accepts a file whose proof no longer opens with a second `by`; counts the judge's runs."""
    def __init__(self):
        self.judged = 0

    def judge_text(self, text):
        self.judged += 1
        ok = not text[len(PREFIX):].lstrip().startswith("by")
        return {"verdict": "accept" if ok else "reject", "output": "" if ok else "t.lean:2:2: error: unexpected token 'by'"}

    def run_lean(self, text):
        return "", 0


class ToolNames(unittest.TestCase):
    def test_a_recorded_closer_maps_to_its_tactic(self):
        self.assertEqual([toolscore.closer_tool(c) for c in ("omega", "norm_num", "simp", "aesop", "exact Nat.le_of_lt h")],
                         ["omega", "(norm_num; done)", "(simp; done)", "(aesop; done)", "exact?"])

    def test_an_all_goals_hole_names_no_single_closer(self):
        self.assertIsNone(toolscore.closer_tool(subgoals.AUTO))
        self.assertIsNone(toolscore.closer_tool("ring_nf"))

    def test_tools_used_in_chain_order_each_once(self):
        self.assertEqual(toolscore.tools_used(["layout", "names"], ["omega", "omega", "linarith", subgoals.AUTO]),
                         ["layout", "names", "omega", "linarith"])

    def test_every_tool_has_a_job(self):
        self.assertTrue(all(toolscore.TOOLS.values()))
        self.assertEqual(set(subgoals.AUTO_TACTICS) | set(toolscore.FIXER_PASSES), set(toolscore.TOOLS))

    def test_halves_split_by_parity(self):
        self.assertEqual((toolscore.half(7), toolscore.half(8)), ("report", "tune"))


class Arms(unittest.TestCase):
    def test_closers_rerun_only_on_a_turn_passes_always(self):
        turn = {"fixes": ["names"], "c_verdict": "accept", "rep": {"closers": ["omega"]}}
        miss = {"fixes": ["names"], "c_verdict": "reject", "rep": {"closers": ["omega"]}}
        self.assertEqual(toolscore.arms_to_run(turn), ["names", "omega"])
        self.assertEqual(toolscore.arms_to_run(miss), ["names"])

    def test_skipping_a_pass_leaves_it_out(self):
        self.assertEqual(fixer.fix("  by\n    exact h\n")[1], ["double_by"])
        self.assertEqual(fixer.fix("  by\n    exact h\n", skip=("double_by",))[1], [])

    def test_the_closers_list_is_what_the_automation_tries(self):
        seen = []
        with mock.patch.object(subgoals, "holes", return_value=[]):
            subgoals.automate_and_goals("x", 1, lambda t: (seen.append(t), ("", 0))[1], tactics=["omega"])
        self.assertTrue(seen)

    def test_grade_one_pairs_the_full_chain_with_each_tool_out(self):
        lean = FakeLean()
        with mock.patch.object(subgoals, "repair", return_value={"stopped": "no holes"}):
            rows = toolscore.grade_one({"proof": "by\n  rfl\n", "lean_output": "t.lean:2:2: error: unexpected token 'by'"},
                                       PREFIX, (None, None), lean)
        self.assertEqual([(t, arm, v) for t, arm, v, *_ in rows],
                         [("*", "full", "accept"), ("double_by", "without", "reject")])     # the turn needed double_by


if __name__ == "__main__":
    unittest.main()
