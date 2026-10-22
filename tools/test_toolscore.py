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

    def test_the_speed_receipt_runs_the_whole_chain_only(self):
        lean = FakeLean()
        with mock.patch.object(subgoals, "repair", return_value={"stopped": "no holes"}):
            rows = toolscore.grade_one({"proof": "by\n  rfl\n", "lean_output": "t.lean:2:2: error: unexpected token 'by'"},
                                       PREFIX, (None, None), lean, full_only=True)
        self.assertEqual([(t, arm, v) for t, arm, v, *_ in rows], [("*", "full", "accept")])


if __name__ == "__main__":
    unittest.main()


class Resolve(unittest.TestCase):
    """The re-solve layer (task #191 step 2): a frozen weekly sample, owed tries resumed by key, one cold try."""
    @staticmethod
    def report(n, tset="primer"):
        """n distinct problems on the report half."""
        out, i = [], 0
        while len(out) < n:
            if toolscore.problem_half(tset, f"p{i}") == "report":
                out.append(f"p{i}")
            i += 1
        return out

    def test_weeks_are_mondays_utc(self):
        self.assertEqual(toolscore.week_of("2026-10-18T23:59:00+00:00"), "2026-10-12")
        self.assertEqual(toolscore.week_of("2026-10-19T00:00:00+00:00"), "2026-10-19")

    def test_the_sample_takes_solved_then_and_open_then_from_finished_weeks_only(self):
        a, b, c, d = self.report(4)
        rows = [{"ts": "2026-10-13T01:00:00+00:00", "target_set": "primer", "target": a, "verdict": "accept"},
                {"ts": "2026-10-13T02:00:00+00:00", "target_set": "primer", "target": b, "verdict": "reject"},
                {"ts": "2026-10-20T02:00:00+00:00", "target_set": "primer", "target": b, "verdict": "accept"},
                {"ts": "2026-10-14T02:00:00+00:00", "target_set": "primer", "target": c, "verdict": "reject"},
                {"ts": "2026-10-20T03:00:00+00:00", "target_set": "primer", "target": d, "verdict": "reject"}]
        got = toolscore.freeze_sample(rows, "2026-10-22T00:00:00+00:00", set(), lambda s, t: "sha", per_week=(3, 3))
        kinds = {(g["target"], g["kind"]) for g in got}
        self.assertEqual(kinds, {(a, "solved_then"), (b, "open_then"), (c, "open_then")})
        self.assertTrue(all(g["week"] == "2026-10-12" for g in got), "the current week is never frozen")
        self.assertEqual(toolscore.freeze_sample(rows, "2026-10-22T00:00:00+00:00", {"2026-10-12"}, lambda s, t: "sha"),
                         [], "a frozen week is never re-drawn")
        self.assertEqual(toolscore.freeze_sample(rows, "2026-10-22T00:00:00+00:00", set(), lambda s, t: None), [],
                         "a problem whose file is gone is not frozen")

    def test_the_tune_half_never_enters_the_sample(self):
        i = 0
        while toolscore.problem_half("primer", f"q{i}") == "report":
            i += 1
        rows = [{"ts": "2026-10-13T01:00:00+00:00", "target_set": "primer", "target": f"q{i}", "verdict": "accept"}]
        self.assertEqual(toolscore.freeze_sample(rows, "2026-10-22T00:00:00+00:00", set(), lambda s, t: "x"), [])

    def test_owed_tries_resume_by_key(self):
        s = {"week": "2026-10-12", "target_set": "primer", "target": "p1", "kind": "open_then", "statement_sha": "x"}
        done = {("2026-10-19", "c1", "lane", "2026-10-12", "primer", "p1", 1)}
        q = toolscore.resolve_queue([s], done, "2026-10-19", "c1", "lane", 0, 1, tries=3)
        self.assertEqual([t for _, t in q], [2, 3])
        self.assertEqual(len(toolscore.resolve_queue([s], done, "2026-10-19", "c2", "lane", 0, 1, tries=3)), 3,
                         "a new chain owes every try again")
        self.assertEqual(sum(len(toolscore.resolve_queue([s], set(), "w", "c", "l", k, 3)) for k in range(3)), 3,
                         "slices split the queue, every try in exactly one")

    def test_an_error_row_leaves_its_try_owed(self):
        row = {"run_week": "w", "chain": "c", "lane": "l", "week": "2026-10-12", "target_set": "primer", "target": "p1",
               "try": 1}
        self.assertEqual(toolscore.resolved_keys([{**row, "verdict": "error"}]), set())
        self.assertEqual(len(toolscore.resolved_keys([{**row, "verdict": "reject"}])), 1)

    def test_slices_share_the_report_half_evenly(self):
        sample = [{"week": "w", "target_set": "minif2f/test", "target": t, "kind": "open_then", "statement_sha": "x"}
                  for t in self.report(60, "minif2f/test")]
        loads = [len(toolscore.resolve_queue(sample, set(), "r", "c", "l", k, 6, tries=1)) for k in range(6)]
        self.assertEqual(sum(loads), 60)
        self.assertTrue(all(n > 0 for n in loads), f"every slice gets work: {loads}")

    S = {"week": "2026-10-12", "target_set": "primer", "target": "t", "kind": "open_then", "statement_sha": "x"}

    def test_router_errors_are_retried_and_kept_apart_from_tries(self):
        calls = []
        def ask(prompt):
            calls.append(prompt)
            raise RuntimeError("HTTP 504 : timed out")
        r = toolscore.resolve_one(self.S, 1, PREFIX + " sorry", PREFIX, ask, FakeLean().judge_text, None, retries=2)
        self.assertEqual((r["verdict"], r["router_errors"], len(calls)), ("error", 3, 3))
        self.assertNotIn("cold", r, "an error is not a try")

    def test_a_refused_lane_stops_the_run(self):
        def ask(prompt):
            raise RuntimeError("HTTP 503 : minimax is gated: the 'sparebrains' share is spent")
        self.assertIsNone(toolscore.resolve_one(self.S, 1, "x", PREFIX, ask, FakeLean().judge_text, None))

    def test_the_cold_prompt_is_the_statement_only_and_the_chain_runs_on_a_reject(self):
        import attempt
        seen, chained = [], []
        def ask(prompt):
            seen.append(prompt)
            return "```lean\n" + PREFIX + "\n  by rfl\n```", {"returned_backend": "lane"}
        chain = lambda proof, prefix, said: chained.append(proof) or {"c_verdict": "accept", "fixes": ["double_by"],
                                                                     "rep": {}}
        r = toolscore.resolve_one(self.S, 1, PREFIX + " sorry", PREFIX, ask, FakeLean().judge_text, chain)
        self.assertEqual(seen, [attempt.ASK + PREFIX + " sorry"])
        self.assertEqual((r["cold"], r["verdict"], r["fixes"]), ("reject", "accept", ["double_by"]))
        self.assertEqual(len(chained), 1)
