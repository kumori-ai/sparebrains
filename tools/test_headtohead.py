"""The head-to-head (tools/headtohead.py): a stand-in model and judge, so these test the fairness rules, not Lean."""
import sys, unittest
from pathlib import Path
from unittest import mock

sys.path[:0] = [str(Path(__file__).resolve().parent)]
import decompose, headtohead as h

TARGET = "import Mathlib\n\nopen Real\n\ntheorem t1 (x : ℝ) (h : 0 < x) : 0 < x ^ 2 := by\n  sorry\n"


def answer(body):
    return f"```lean4\ntheorem t1 (x : ℝ) (h : 0 < x) : 0 < x ^ 2 := by\n{body}```"


class Fairness(unittest.TestCase):
    def test_the_set_is_fixed_by_the_seed_not_by_results(self):
        targets = {"open": [{"target_set": "s", "target": f"o{i}", "order": 9 - i} for i in range(5)],
                   "solved": [{"target_set": "s", "target": f"d{i}", "rung": r} for i, r in
                              enumerate(["aime", "primer", "imo", "math-L1", "custom"])]}
        a = h.pick(targets, 2, 2, lambda t: True)
        self.assertEqual(a, h.pick(targets, 2, 2, lambda t: True))
        self.assertEqual([t["target"] for t in a[:2]], ["o4", "o3"])            # the open list's order
        self.assertTrue(all(t["rung"] in h.HARD_RUNGS for t in a[2:]))           # primer and L1 never picked
        self.assertEqual([t["status"] for t in a], ["open", "open", "solved", "solved"])

    def test_slices_split_the_open_list_by_name_whatever_is_solved_between_them(self):
        opened = [{"target_set": "s", "target": f"o{i}", "order": i} for i in range(40)]
        names = lambda ts: {t["target"] for t in ts}
        halves = [names(h.pick({"open": opened, "solved": []}, 99, 0, lambda t: True, (k, 2))) for k in (0, 1)]
        self.assertEqual((halves[0] & halves[1], halves[0] | halves[1]), (set(), names(opened)))
        gone = min(halves[0])                                                    # solved by half 0's run
        later = {"open": [t for t in opened if t["target"] != gone], "solved": []}
        self.assertEqual(names(h.pick(later, 99, 0, lambda t: True, (1, 2))), halves[1])

    def test_a_replication_draws_fresh_solved_problems_and_leaves_the_slices_alone(self):
        targets = {"open": [{"target_set": "s", "target": f"o{i}", "order": i} for i in range(20)],
                   "solved": [{"target_set": "s", "target": f"d{i}", "rung": "amc12"} for i in range(40)]}
        names = lambda ts: [t["target"] for t in ts]
        first = h.pick(targets, 0, 10, lambda t: True)
        again = h.pick(targets, 0, 10, lambda t: True, seed="replication", used=set(names(first)))
        self.assertEqual(len(again), 10)
        self.assertFalse(set(names(first)) & set(names(again)))
        self.assertEqual(names(h.pick(targets, 99, 0, lambda t: True, (1, 2))),
                         names(h.pick(targets, 99, 0, lambda t: True, (1, 2), seed="replication")))

    def test_the_sign_test_matches_the_runs_we_reported(self):
        self.assertEqual(round(h.sign_p(8, 1), 4), 0.0391)          # run 39271052543
        self.assertEqual(round(h.sign_p(7, 2), 4), 0.1797)          # the one-flip check
        self.assertEqual(round(h.sign_p(6, 0), 4), 0.0312)          # the plan arm's smallest pass
        self.assertEqual(h.sign_p(0, 0), 1.0)
        self.assertIn("p", h.summary([{"arm": "tools", "target": "a", "outcome": "solved", "calls": 1, "tokens": 1,
                                       "seconds": 1}, {"arm": "alone", "target": "a", "outcome": "failed", "calls": 1,
                                       "tokens": 1, "seconds": 1}]))

    def test_the_goal_is_the_theorem_itself(self):
        self.assertEqual(h.theorem_as_goal(TARGET), "theorem sb_goal (x : ℝ) (h : 0 < x) : 0 < x ^ 2 := by")

    def test_alone_judges_the_raw_answer_and_stops_at_the_first_accept(self):
        replies = iter([answer("  nlinarith\n"), answer("  positivity\n"), answer("  positivity\n")])
        judged = []
        judge = lambda t: (judged.append(t), {"verdict": "accept" if "positivity" in t else "reject"})[1]
        cand, k = h.alone(TARGET, lambda p: next(replies), judge, calls=4)
        self.assertEqual(k, 2)
        self.assertEqual(len(judged), 2)                     # no fixer, no loop: one judge per answer

    def test_alone_gives_up_after_its_budget(self):
        calls = []
        cand, k = h.alone(TARGET, lambda p: (calls.append(p), answer("  nlinarith\n"))[1],
                          lambda t: {"verdict": "reject"}, calls=3)
        self.assertEqual((cand, k, len(calls)), (None, None, 3))

    def test_tools_get_the_same_budget(self):
        seen = {}
        def fake(statement, prefix, **kw):
            seen.update(kw["budget"])
            return None
        with mock.patch.object(decompose, "decompose", side_effect=fake):
            h.with_tools(TARGET, None, None, lambda t: {"verdict": "reject"}, calls=3)
        self.assertEqual(seen["max"], 3)

    def test_both_arms_run_on_every_problem_in_a_seeded_order(self):
        t = {"target_set": "s", "target": "t1", "status": "solved", "rung": "aime"}
        call = lambda p: {"text": answer("  positivity\n"), "tokens": 10}
        with mock.patch.object(decompose, "decompose", return_value="  positivity\n"):
            rows, solves = h.run([t], lambda s, n: TARGET, call, None, lambda x: {"verdict": "accept"}, calls=2)
        self.assertEqual(sorted(r["arm"] for r in rows), ["alone", "tools"])
        self.assertEqual(solves, [])                         # a solved problem is measured, never re-published
        rows2, _ = h.run([t], lambda s, n: TARGET, call, None, lambda x: {"verdict": "accept"}, calls=2)
        self.assertEqual([r["arm"] for r in rows], [r["arm"] for r in rows2])

    def test_the_lessons_arm_is_alone_with_the_block_in_front_and_the_same_budget(self):
        t = {"target_set": "s", "target": "t1", "status": "solved", "rung": "aime"}
        prompts = []
        call = lambda p: (prompts.append(p), {"text": answer("  positivity\n"), "tokens": 10})[1]
        rows, _ = h.run([t], lambda s, n: TARGET, call, None, lambda x: {"verdict": "accept"}, calls=2,
                        arms=("alone", "lessons"), lesson_block=lambda s, n, text: "## Lessons: 1 solved theorem\n")
        self.assertEqual(sorted(r["arm"] for r in rows), ["alone", "lessons"])
        self.assertEqual(sum(p.startswith("## Lessons") for p in prompts), 1)
        self.assertTrue(all(p.endswith("```") for p in prompts))     # the target file follows the block unchanged

    def test_the_lessons_arm_records_which_retrieval_it_got(self):
        t = {"target_set": "s", "target": "t1", "status": "solved", "rung": "aime"}
        call = lambda p: {"text": answer("  positivity\n"), "tokens": 10}
        rows, _ = h.run([t], lambda s, n: TARGET, call, None, lambda x: {"verdict": "accept"}, calls=2,
                        arms=("alone", "lessons"),
                        lesson_block=lambda s, n, text: ("## Lessons: 1 solved theorem\n", {"by": "conclusion", "goals": 2}))
        by_arm = {r["arm"]: r for r in rows}
        self.assertEqual(by_arm["lessons"]["lessons"], {"by": "conclusion", "goals": 2})
        self.assertNotIn("lessons", by_arm["alone"])

    def test_a_router_lane_answers_in_leanstral_shape_and_waits_out_a_429(self):
        from utilities.kumori_api_client import KumoriAPIError
        calls, slept = [], []
        def llm_chat(backend, messages, **kw):
            calls.append((backend, messages[0]["content"], kw))
            if len(calls) == 1:
                raise KumoriAPIError("per-lane RPM spacing", status_code=429, retry_after=2)
            return answer("  positivity\n"), backend, {"usage": {"completion_tokens": 12}, "finish_reason": "stop"}
        call = h.router_call("mistral-ministral-8b-2512", llm_chat, sleep=slept.append)
        r = call("prove it")
        self.assertEqual((r["text"], r["tokens"], r["finish"]), (answer("  positivity\n"), 12, "stop"))
        self.assertEqual(slept, [2])
        self.assertEqual([c[0] for c in calls], ["mistral-ministral-8b-2512"] * 2)
        self.assertTrue(all(c[2]["system"] and c[2]["app_name"] == "sparebrains" and c[2]["include_metadata"] for c in calls))
        def refuse(backend, messages, **kw):
            raise KumoriAPIError("pool_gated", status_code=403)
        self.assertIn("error", h.router_call("x", refuse, sleep=slept.append)("prove it"))   # a refusal is an error row, no wait
        self.assertEqual(h.lane_of("mistral-ministral-8b-2512")["provider"], "mistral")

    def test_same_as_names_the_exact_problems_of_an_earlier_run_in_its_order(self):
        rows = [{"target_set": "s", "target": "b", "status": "solved", "rung": "aime", "arm": "alone"},
                {"target_set": "s", "target": "b", "status": "solved", "rung": "aime", "arm": "lessons"},
                {"target_set": "s", "target": "a", "status": "open", "rung": None, "arm": "alone"}]
        self.assertEqual([(t["target"], t["status"]) for t in h.same_set(rows)], [("b", "solved"), ("a", "open")])

    def test_a_call_with_no_token_count_makes_the_row_and_the_summary_null_not_zero(self):
        t = {"target_set": "s", "target": "t1", "status": "solved", "rung": "aime"}
        n = [0]
        def call(p):
            n[0] += 1
            return {"text": answer("  positivity\n"), "tokens": None if n[0] == 1 else 10, "finish": "length", "backend": "lane-x"}
        rows, _ = h.run([t], lambda s, n: TARGET, call, None, lambda x: {"verdict": "reject"}, calls=2,
                        arms=("alone", "lessons"), lesson_block=lambda s, n, text: "## Lessons\n", writer="lane-x")
        first = next(r for r in rows if r["calls"] == 2 and r["tokens"] is None)      # the arm whose first call was unmetered
        self.assertEqual((first["cut"], first["errors"], first["writer"], first["served"]), (2, 0, "lane-x", ["lane-x"]))
        self.assertIsNone(h.summary(rows)[first["arm"]]["tokens_per_solve"])
        err_rows, _ = h.run([t], lambda s, n: TARGET, lambda p: {"error": "pool_gated"}, None,
                            lambda x: {"verdict": "reject"}, calls=2, arms=("alone", "lessons"),
                            lesson_block=lambda s, n, text: "## Lessons\n", writer="lane-x")
        self.assertEqual({(r["errors"], r["tokens"], tuple(r["served"])) for r in err_rows}, {(2, None, ())})   # an error's usage is unknown
        k = [0]
        def err_then_solve(p):                           # Codex round 2, f3: an error then a metered solve is still unknown
            k[0] += 1
            return {"error": "timeout"} if k[0] % 2 else {"text": answer("  positivity\n"), "tokens": 10}
        mixed, _ = h.run([t], lambda s, n: TARGET, err_then_solve, None, lambda x: {"verdict": "accept"}, calls=2,
                         arms=("alone", "lessons"), lesson_block=lambda s, n, text: "## Lessons\n")
        self.assertEqual({(r["outcome"], r["calls"], r["errors"], r["tokens"]) for r in mixed}, {("solved", 2, 1, None)})
        self.assertTrue(all(h.summary(mixed)[a]["tokens_per_solve"] is None for a in ("alone", "lessons")))

    def test_the_summary_counts_the_paired_disagreements(self):
        rows = [{"arm": "alone", "target": "a", "outcome": "failed", "calls": 4, "tokens": 40, "seconds": 9},
                {"arm": "tools", "target": "a", "outcome": "solved", "calls": 2, "tokens": 30, "seconds": 20},
                {"arm": "alone", "target": "b", "outcome": "solved", "calls": 1, "tokens": 10, "seconds": 5},
                {"arm": "tools", "target": "b", "outcome": "solved", "calls": 1, "tokens": 12, "seconds": 8}]
        s = h.summary(rows)
        self.assertEqual((s["only_tools"], s["only_alone"]), (["a"], []))
        self.assertEqual((s["alone"]["solved"], s["tools"]["solved"]), (1, 2))
        self.assertEqual(s["alone"]["calls_per_solve"], 5.0)   # every call the arm spent, over its solves
        self.assertEqual(s["tools"]["calls_per_solve"], 1.5)

    def test_the_summary_pairs_whichever_treatment_arm_ran_against_alone(self):
        row = lambda arm, t, out: {"arm": arm, "target": t, "outcome": out, "calls": 1, "tokens": 1, "seconds": 1}
        both = [row(a, t, "solved") for t in "abcdef" for a in ("alone", "lessons")]
        s = h.summary(both)                                     # six ties: no disagreement, p = 1
        self.assertEqual((s["only_lessons"], s["only_alone_vs_lessons"], s["p_lessons"]), ([], [], 1.0))
        self.assertNotIn("p", s)                                 # no tools arm ran: no tools-vs-alone number is faked
        wins = [row("alone", "a", "failed"), row("lessons", "a", "solved"), row("alone", "b", "solved"), row("lessons", "b", "failed"),
                row("alone", "c", "failed"), row("lessons", "c", "solved")]
        s = h.summary(wins)
        self.assertEqual((s["only_lessons"], s["only_alone_vs_lessons"]), (["a", "c"], ["b"]))
        self.assertEqual(s["p_lessons"], 1.0)                    # 2 vs 1 is no evidence


if __name__ == "__main__":
    unittest.main()
