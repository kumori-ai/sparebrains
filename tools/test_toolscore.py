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
        done = {("2026-10-19", "c1", "lane", "weekly", "2026-10-12", "primer", "p1", 1)}
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

    def test_a_lane_kumori_no_longer_has_is_gone_not_refused(self):
        # 2026-10-24: openrouter-minimax-m3-1-flash answered "HTTP 404 : unknown backend" and every nightly re-solve
        # stopped as if its share were spent, 0 tries in 4 runs. A gone lane must say so, loudly.
        def ask(prompt):
            raise RuntimeError("kumori /api/v1/llm/chat HTTP 404 : unknown backend: openrouter-minimax-m3-1-flash")
        with self.assertRaises(toolscore.LaneGone):
            toolscore.resolve_one(self.S, 1, "x", PREFIX, ask, FakeLean().judge_text, None)

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
        self.assertIn("chain_seconds", r, "the chain is timed too")
        self.assertEqual(len(chained), 1)


class SpeedReport(unittest.TestCase):
    SAMPLE = [{"week": "2026-10-12", "target_set": "s", "target": x, "kind": k, "statement_sha": "x"}
              for x, k in (("a", "open_then"), ("b", "open_then"), ("c", "open_then"), ("d", "open_then"),
                           ("e", "solved_then"), ("f", "open_then"))]

    @staticmethod
    def row(target, t, verdict, ts, cold=None, lane="l"):
        return {"run_week": "2026-10-19", "chain": "c", "lane": lane, "week": "2026-10-12", "target_set": "s",
                "target": target, "try": t, "verdict": verdict, "cold": cold or verdict, "ts": ts,
                "call_seconds": 10, "lean_seconds": 5, "chain_seconds": 0}

    def test_the_population_is_the_frozen_sample_and_calls_count_answers_in_order(self):
        rows = [self.row("a", 2, "accept", "T2", cold="reject"), {**self.row("a", 1, "reject", "T1"), "verdict": "error"},
                self.row("b", 1, "reject", "T1"), self.row("b", 2, "reject", "T2"), self.row("b", 3, "reject", "T3"),
                self.row("c", 1, "reject", "T1"),
                {**self.row("d", 1, "accept", "T1"), "verdict": "error"},
                self.row("e", 3, "reject", "T1"), self.row("e", 1, "accept", "T2")]   # slot 1 filled later
        (r,) = toolscore.speed_report(rows, self.SAMPLE)
        self.assertEqual(r["problems"], 6, "every frozen problem, f never tried")
        self.assertEqual((r["solved"], r["censored"], r["owed"]), (2, 1, 3), "a and e solved; b censored; c, d, f owed")
        self.assertEqual(sorted(r["calls_to_first"]), [1, 2], "a: 1 answer (the error is no call); e: 2nd answer")
        self.assertEqual((r["open_then_solved"], r["turned"]), (1, 1))
        self.assertIn(15.0, r["seconds_to_first"])

    def test_lanes_are_kept_apart_and_shown(self):
        rows = [self.row("a", 1, "accept", "T1", lane="l1"), self.row("a", 1, "reject", "T1", lane="l2")]
        rep = toolscore.speed_report(rows, self.SAMPLE[:1])
        self.assertEqual([(r["lane"], r["solved"]) for r in rep], [("l1", 1), ("l2", 0)])
        self.assertIn("| l1 |", toolscore.render_speed(rep))
        self.assertIn("among solved", toolscore.render_speed(rep))


class SizeSeries(unittest.TestCase):
    """The size series (2026-10-24, non-negotiable 6): solved targets re-run by one family at three sizes with this
    week's chain. Codex 20261024T150248489394Z and 20261024T150510924100Z shaped it."""
    CUT = "2026-10-24T00:00:00+00:00"

    def solved_rows(self, n, rung_of):
        names = Resolve.report(n)
        return names, [{"ts": "2026-10-10T00:00:00+00:00", "target_set": "primer", "target": t, "verdict": "accept",
                        "rung": rung_of(i)} for i, t in enumerate(names)]

    def test_the_solved_sample_is_frozen_per_rung_with_weights_and_its_own_cohort(self):
        names, rows = self.solved_rows(30, lambda i: "primer" if i < 24 else "mil")
        rows.append({"ts": "2026-10-25T00:00:00+00:00", "target_set": "primer", "target": "late", "verdict": "accept",
                     "rung": "primer"})
        got = toolscore.freeze_solved(rows, self.CUT, lambda s, t: "sha", n=10, min_per_rung=3)
        by = {}
        for g in got:
            by.setdefault(g["rung"], []).append(g)
        self.assertEqual({r: len(v) for r, v in by.items()}, {"primer": 7, "mil": 3})
        self.assertEqual({g["cohort"] for g in got}, {"solved"})
        self.assertAlmostEqual(by["primer"][0]["weight"], 24 / 7)
        self.assertEqual(by["mil"][0]["weight"], 2.0)
        self.assertNotIn("late", {g["target"] for g in got}, "solved after the cutoff is not eligible")
        self.assertTrue(all(toolscore.problem_half(g["target_set"], g["target"]) == "report" for g in got))
        self.assertEqual(got, toolscore.freeze_solved(rows, self.CUT, lambda s, t: "sha", n=10, min_per_rung=3))

    def test_cohorts_never_mix_in_keys_freezing_or_queues(self):
        weekly = {"week": "2026-10-12", "target_set": "primer", "target": "a", "kind": "solved_then", "statement_sha": "s"}
        solved = {"week": "solved-2026-10-24", "target_set": "primer", "target": "a", "cohort": "solved",
                  "statement_sha": "s", "rung": "primer", "weight": 1.0}
        self.assertEqual(toolscore.cohort_of(weekly), "weekly")
        self.assertEqual(toolscore.frozen_weekly_weeks([weekly, solved]), {"2026-10-12"})
        q = toolscore.resolve_queue([weekly, solved], set(), "2026-10-19", "c", "lane-3b", 0, 1, cohort="solved")
        self.assertEqual({s["week"] for s, _ in q}, {"solved-2026-10-24"})
        row = {"run_week": "2026-10-19", "chain": "c", "lane": "lane-3b", "week": "solved-2026-10-24",
               "target_set": "primer", "target": "a", "try": 1, "verdict": "reject", "cohort": "solved"}
        self.assertIn(("2026-10-19", "c", "lane-3b", "solved", "solved-2026-10-24", "primer", "a", 1),
                      toolscore.resolved_keys([row]))

    def test_a_problem_stops_at_its_first_raw_accept(self):
        solved = {"week": "solved-2026-10-24", "target_set": "primer", "target": "a", "cohort": "solved",
                  "statement_sha": "s"}
        row = {"run_week": "w", "chain": "c", "lane": "l", "week": "solved-2026-10-24", "target_set": "primer",
               "target": "a", "try": 1, "verdict": "accept", "cold": "accept", "cohort": "solved"}
        q = toolscore.resolve_queue([solved], toolscore.resolved_keys([row]), "w", "c", "l", 0, 1, cohort="solved",
                                    raw_solved=toolscore.raw_solved([row]))
        self.assertEqual(q, [])

    def test_the_answer_and_its_requests_are_kept_even_when_empty(self):
        calls = []
        def ask(prompt):
            calls.append(1)
            if len(calls) == 1:
                raise RuntimeError("HTTP 502 : bad gateway")
            return "no lean here", {"returned_backend": "l", "inference": {"returned_model": "m"}}
        r = toolscore.resolve_one(Resolve.S, 1, PREFIX + " sorry", PREFIX, ask, FakeLean().judge_text, None)
        self.assertEqual((r["verdict"], r["answer"], r["requests"]), ("reject", "", 2))
        self.assertEqual(r["returned_model"], "m")

    def test_a_gone_lane_does_not_stop_the_others_and_the_cap_holds(self):
        sample = [{"week": "solved-x", "target_set": "primer", "target": t, "cohort": "solved", "statement_sha": "s"}
                  for t in ("a", "b")]
        def ask_for(lane):
            def ask(prompt):
                if lane == "gone":
                    raise RuntimeError("HTTP 404 : unknown backend: gone")
                return "```lean\n" + PREFIX + "\n  rfl\n```", {"returned_backend": lane, "inference": {}}
            return ask
        written = []
        gone = toolscore.resolve_round([(s, 1) for s in sample], ["gone", "ok"], ask_for,
                                       lambda s: (PREFIX + " sorry", PREFIX), FakeLean().judge_text, None,
                                       written.append, max_requests=100)
        self.assertEqual(gone, ["gone"])
        self.assertEqual(sorted((w["lane"], w["target"]) for w in written if w["verdict"] != "lane_gone"),
                         [("ok", "a"), ("ok", "b")])
        written = []
        toolscore.resolve_round([(s, 1) for s in sample], ["ok"], ask_for, lambda s: (PREFIX + " sorry", PREFIX),
                                FakeLean().judge_text, None, written.append, max_requests=1)
        self.assertEqual(len(written), 1, "the cap counts requests, retries included")

    def test_the_report_gives_each_arm_its_own_cost_and_an_interval(self):
        sample = [{"week": "solved-x", "target_set": "primer", "target": t, "cohort": "solved", "rung": "primer",
                   "weight": 1.0} for t in ("a", "b", "c")]
        def r(t, try_no, cold, verdict, ts):
            return {"run_week": "w", "chain": "c", "lane": "l", "cohort": "solved", "week": "solved-x",
                    "target_set": "primer", "target": t, "try": try_no, "cold": cold, "verdict": verdict, "ts": ts,
                    "requests": 1, "response_chars": 100}
        rows = [r("a", 1, "reject", "accept", "1"), r("a", 2, "accept", "accept", "2"),      # tools first, raw at 2
                r("b", 1, "reject", "reject", "3"), r("b", 2, "reject", "reject", "4"), r("b", 3, "reject", "reject", "5"),
                r("c", 1, "accept", "accept", "6")]
        rep = toolscore.size_report(rows, sample)[0]
        self.assertEqual((rep["raw"]["solved"], rep["assisted"]["solved"], rep["problems"]), (2, 2, 3))
        self.assertEqual(rep["raw"]["attempts_to_first"], [1, 2])
        self.assertEqual(rep["assisted"]["attempts_to_first"], [1, 1])
        self.assertEqual(rep["raw"]["not_solved_within"], 1)
        lo, hi = rep["raw"]["wilson95"]
        self.assertTrue(0 < lo < 2 / 3 < hi < 1)
        self.assertIsNone(toolscore.size_report([r("b", 1, "reject", "reject", "1")], sample[1:2])[0]["raw"]["yield"])

    def test_the_deadline_stops_a_round(self):
        sample = [{"week": "solved-x", "target_set": "primer", "target": "a", "cohort": "solved", "statement_sha": "s"}]
        written = []
        toolscore.resolve_round([(sample[0], 1)], ["ok"], lambda lane: (lambda p: ("x", {})),
                                lambda s: (PREFIX + " sorry", PREFIX), FakeLean().judge_text, None, written.append,
                                deadline=0)
        self.assertEqual(written, [])


class SizeSeriesFixes(unittest.TestCase):
    """Codex 20261024T151621770745Z on the first build: the cap per request, refusals counted, gone survives a crash,
    the weekly series unchanged, each arm's own request and char cost, error-only lanes shown."""
    ITEM = {"week": "solved-x", "target_set": "primer", "target": "a", "cohort": "solved", "statement_sha": "s"}
    TEXT = staticmethod(lambda s: (PREFIX + " sorry", PREFIX))

    def test_the_cap_counts_every_request_retries_included(self):
        asked = []
        def ask_for(lane):
            def ask(prompt):
                asked.append(lane)
                raise RuntimeError("HTTP 502 : bad gateway")
            return ask
        budget = toolscore.Budget(2)
        toolscore.resolve_round([(self.ITEM, 1)], ["l"], ask_for, self.TEXT, FakeLean().judge_text, None,
                                lambda r: None, budget)
        self.assertEqual((len(asked), budget.left), (2, 0))

    def test_a_refusal_spends_from_the_same_budget_as_the_next_cohort(self):
        def ask_for(lane):
            def ask(prompt):
                raise RuntimeError("HTTP 503 : l is gated")
            return ask
        budget = toolscore.Budget(5)
        toolscore.resolve_round([(self.ITEM, 1)], ["l"], ask_for, self.TEXT, FakeLean().judge_text, None,
                                lambda r: None, budget)
        self.assertEqual(budget.left, 4)

    def test_a_gone_lane_still_ends_red_when_a_later_round_crashes(self):
        def crash(gone):
            raise OSError("disk full")
        self.assertEqual(toolscore.run_rounds([lambda gone: gone.append("gone-lane"), crash]), toolscore.GONE_EXIT)
        with self.assertRaises(OSError):
            toolscore.run_rounds([lambda gone: None, crash])

    def test_a_gone_lane_still_ends_red_when_its_own_round_crashes(self):
        # Codex 20261024T152323969171Z: lane_gone recorded, then the judge crashed in the same round
        def ask_for(lane):
            def ask(prompt):
                if lane == "gone":
                    raise RuntimeError("HTTP 404 : unknown backend: gone")
                return "```lean\n" + PREFIX + "\n  rfl\n```", {}
            return ask
        def judge(text):
            raise OSError("judge crash")
        item = {**self.ITEM, "target": "t"}
        round_ = lambda gone: toolscore.resolve_round([(item, 1)], ["gone", "ok"], ask_for, self.TEXT, judge, None,
                                                      lambda r: None, toolscore.Budget(9), gone=gone)
        self.assertEqual(toolscore.run_rounds([round_]), toolscore.GONE_EXIT)

    def test_every_request_spent_is_on_the_record(self):
        # Codex 20261024T152323969171Z: a cap that cuts retries, or a refusal, must still leave its requests in a row
        def failing(prompt):
            raise RuntimeError("HTTP 502 : bad gateway")
        def gated(prompt):
            raise RuntimeError("HTTP 503 : l is gated")
        for ask, verdict in ((failing, "error"), (gated, "refused")):
            written = []
            toolscore.resolve_round([(self.ITEM, 1)], ["l"], lambda lane: ask, self.TEXT, FakeLean().judge_text, None,
                                    written.append, toolscore.Budget(2))
            self.assertEqual([(w["verdict"], w["requests"]) for w in written],
                             [(verdict, 2 if verdict == "error" else 1)])
        self.assertEqual(toolscore.resolved_keys([{**written[0], "run_week": "w", "chain": "c"}]), set(),
                         "a refused try stays owed")

    def test_the_weekly_series_keeps_all_three_tries_after_a_raw_accept(self):
        item = {**self.ITEM, "target": "t"}                     # the answer's theorem is `t`, so it is extracted
        weekly = {**item, "cohort": "weekly", "week": "2026-10-12"}
        def ask_for(lane):
            return lambda prompt: ("```lean\n" + PREFIX + "\n  rfl\n```", {})
        written = []
        toolscore.resolve_round([(weekly, t) for t in (1, 2, 3)], ["l"], ask_for, self.TEXT, FakeLean().judge_text,
                                None, written.append, toolscore.Budget(99), stop_at_raw=False)
        self.assertEqual([w["try"] for w in written], [1, 2, 3])
        written = []
        toolscore.resolve_round([(item, t) for t in (1, 2, 3)], ["l"], ask_for, self.TEXT, FakeLean().judge_text,
                                None, written.append, toolscore.Budget(99))
        self.assertEqual([(w["try"], w["cold"]) for w in written], [(1, "accept")],
                         "the solved cohort stops at the first raw accept")

    def test_each_arm_pays_only_up_to_its_own_first_accept_and_error_only_lanes_show(self):
        sample = [{"week": "solved-x", "target_set": "primer", "target": "a", "cohort": "solved", "rung": "primer"}]
        def r(lane, try_no, cold, verdict, ts, req=1, chars=100):
            return {"run_week": "w", "chain": "c", "lane": lane, "cohort": "solved", "week": "solved-x",
                    "target_set": "primer", "target": "a", "try": try_no, "cold": cold, "verdict": verdict, "ts": ts,
                    "requests": req, "response_chars": chars}
        rows = [r("l", 1, "reject", "accept", "1", req=2, chars=10),          # the chain accepts at try 1
                r("l", 2, "accept", "accept", "2", req=3, chars=20),          # raw only at try 2
                {"run_week": "w", "chain": "c", "lane": "dead", "cohort": "solved", "verdict": "lane_gone", "ts": "3"},
                {**r("err", 1, None, "error", "4", req=3), "cold": None}]
        rep = {x["lane"]: x for x in toolscore.size_report(rows, sample)}
        self.assertEqual((rep["l"]["assisted"]["requests"], rep["l"]["assisted"]["chars"]), (2, 10))
        self.assertEqual((rep["l"]["raw"]["requests"], rep["l"]["raw"]["chars"]), (5, 30))
        self.assertTrue(rep["dead"]["gone"])
        self.assertEqual((rep["err"]["raw"]["solved"], rep["err"]["requests"]), (0, 3))


class RepinAndTokens(unittest.TestCase):
    """2026-10-24: the weekly series re-pinned to a live lane (its old one answers 404), and the provider's token counts
    (kumori ef6b11b, #562) recorded beside chars."""

    def test_the_weekly_lane_is_the_repinned_one(self):
        self.assertEqual(toolscore.RESOLVE_LANE, "agnes-agnes-2-5-flash")

    def test_tokens_are_kept_per_try_and_summed_per_arm(self):
        def ask(prompt):
            return "no lean here", {"inference": {"usage": {"prompt_tokens": 300, "completion_tokens": 40,
                                                             "thinking_tokens": 25}}}
        r = toolscore.resolve_one(Resolve.S, 1, PREFIX + " sorry", PREFIX, ask, FakeLean().judge_text, None)
        self.assertEqual((r["prompt_tokens"], r["completion_tokens"], r["thinking_tokens"]), (300, 40, 25))
        sample = [{"week": "solved-x", "target_set": "primer", "target": "a", "cohort": "solved", "rung": "primer"}]
        def row(try_no, cold, verdict, ts, out, think):
            return {"run_week": "w", "chain": "c", "lane": "l", "cohort": "solved", "week": "solved-x",
                    "target_set": "primer", "target": "a", "try": try_no, "cold": cold, "verdict": verdict, "ts": ts,
                    "requests": 1, "completion_tokens": out, "thinking_tokens": think}
        rep = toolscore.size_report([row(1, "reject", "accept", "1", 40, 10), row(2, "accept", "accept", "2", 30, None)],
                                    sample)[0]
        self.assertEqual(rep["assisted"]["output_tokens"], 40, "OpenAI-shaped: thinking is inside completion_tokens")
        self.assertEqual(rep["raw"]["output_tokens"], 70)
        self.assertEqual(rep["raw"]["tries_without_tokens"], 0)

    def test_output_tokens_follow_each_adapters_meaning_and_missing_counts_show(self):
        # Codex 20261024T155243924125Z: OpenAI-shaped completion_tokens already hold the thinking (kumori
        # _backends._usage_from_openai: Groq gpt-oss-20b 52 of 62); Google's own API reports them apart
        self.assertEqual(toolscore.output_tokens({"completion_tokens": 62, "thinking_tokens": 52,
                                                  "returned_backend": "groq-gptoss-20b"}), 62)
        self.assertEqual(toolscore.output_tokens({"completion_tokens": 10, "thinking_tokens": 20,
                                                  "returned_backend": "gemini-2.5-flash"}), 30)
        self.assertIsNone(toolscore.output_tokens({"completion_tokens": None, "thinking_tokens": None}))
        sample = [{"week": "solved-x", "target_set": "primer", "target": "a", "cohort": "solved", "rung": "primer"}]
        row = {"run_week": "w", "chain": "c", "lane": "l", "cohort": "solved", "week": "solved-x", "target_set": "primer",
               "target": "a", "try": 1, "cold": "reject", "verdict": "reject", "ts": "1", "requests": 1}
        table = toolscore.render_size(toolscore.size_report([row], sample))
        self.assertIn("unknown / unknown", table, "no counts at all must not read as 0 tokens")
