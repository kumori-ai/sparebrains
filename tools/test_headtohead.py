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
        self.assertTrue(all(c[2]["long_call"] and c[2]["timeout_s"] >= 120 for c in calls))   # the ladder's cold try, not the 30 s default
        def refuse(backend, messages, **kw):
            raise KumoriAPIError("pool_gated", status_code=403, payload={"error_code": "pool_gated"})
        r = h.router_call("x", refuse, sleep=slept.append)("prove it")
        self.assertEqual((("error" in r), r["reason"], slept), (True, "pool_gated", [2]))      # no clock: the call is lost, no wait
        def benched(backend, messages, **kw):            # run 40977072274: 234 of 240 calls met this and were lost in 2 s each
            raise KumoriAPIError("mistral-ministral-8b-2512 is benched: breaker_open", status_code=503, retry_after=7)
        r = h.router_call("x", benched, tries=2, sleep=slept.append)("prove it")
        self.assertEqual((r["reason"], slept), ("benched", [2, 7]))                           # waited once, then the call is lost, named
        def benched_long(backend, messages, **kw):       # Codex f1 (2026-10-30): the void run's clock was 194 s, over PARK_WAIT_S
            raise KumoriAPIError("x is benched: breaker_open", status_code=503, retry_after=194)
        r = h.router_call("x", benched_long, tries=3, sleep=slept.append)("prove it")
        self.assertEqual((r["reason"], slept[2:]), ("benched", [180, 180]))                   # waited the cap twice, never refused outright
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
        self.assertTrue(all(r["reasons"] == {} for r in rows))                         # error-free rows carry it too (Codex f2)
        first = next(r for r in rows if r["calls"] == 2 and r["tokens"] is None)      # the arm whose first call was unmetered
        self.assertEqual((first["cut"], first["errors"], first["writer"], first["served"]), (2, 0, "lane-x", ["lane-x"]))
        self.assertIsNone(h.summary(rows)[first["arm"]]["tokens_per_solve"])
        err_rows, _ = h.run([t], lambda s, n: TARGET, lambda p: {"error": "pool_gated"}, None,
                            lambda x: {"verdict": "reject"}, calls=2, arms=("alone", "lessons"),
                            lesson_block=lambda s, n, text: "## Lessons\n", writer="lane-x")
        self.assertEqual({(r["errors"], r["tokens"], tuple(r["served"])) for r in err_rows}, {(2, None, ())})   # an error's usage is unknown
        self.assertEqual({tuple(r["reasons"].items()) for r in err_rows}, {(("pool_gated", 2),)})                 # and its reason is on the row
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

class OffBaselineTests(unittest.TestCase):
    def test_off_the_no_model_set_is_reported_beside_the_totals_not_instead(self):
        row = lambda t, arm, won: {"arm": arm, "target_set": "s", "target": t, "outcome": "solved" if won else "failed",
                                   "calls": 1, "tokens": 1, "seconds": 1}
        rows = [row("easy", "alone", False), row("easy", "skeleton", True), row("hard", "alone", False), row("hard", "skeleton", False)]
        base = {"set": {("s", "easy")}, "targets": 2, "version": {"run_id": "1"}}
        plain, split = h.summary(rows, ("alone", "skeleton")), h.summary(rows, ("alone", "skeleton"), baseline=base)
        self.assertEqual(split["skeleton"], plain["skeleton"], "the totals are unchanged")
        self.assertEqual(split["only_skeleton"], ["easy"])
        off = split["off_baseline"]
        self.assertEqual((off["problems_paired"], off["skeleton"]["solved"], off["only_skeleton"]), (1, 0, []))
        self.assertEqual(split["in_baseline"], 1)
        self.assertIn("not accepted by", split["off_baseline_means"])
        unk = h.summary(rows, ("alone", "skeleton"), baseline={**base, "unknown": {("s", "hard")}})
        self.assertEqual((unk["off_baseline"]["problems_paired"], unk["baseline_unknown"]), (0, 1),
                         "a target the baseline never finished is not off it (Codex f3)")


if __name__ == "__main__":
    unittest.main()


class Bounded(unittest.TestCase):
    """Run 40980090085 (2026-10-30): the lane answered nothing, every call waited out its parks, and the job printed
    nothing for 5 h 38 min until the 340-minute timeout cancelled it; the publish step never ran, so 30 problems' worth
    of calls left no row. A run is bounded on its clock and on the lane, and what finished is published."""
    T = [{"target_set": "s", "target": f"t{i}", "status": "solved", "rung": "aime"} for i in range(4)]

    def test_a_lane_that_only_errors_trips_the_breaker_and_the_rest_is_void_not_measured(self):
        n = [0]
        def call(p):
            n[0] += 1
            return {"error": "benched", "reason": "benched"}
        rows, _ = h.run(self.T, lambda s, t: TARGET, call, None, lambda x: {"verdict": "reject"}, calls=4, jobs=1,
                        arms=("alone", "lessons"), lesson_block=lambda s, t, text: "## L\n", breaker=6)
        self.assertEqual(n[0], 6, "after 6 consecutive errored calls the lane is not called again")
        void = [r for r in rows if r.get("void")]
        self.assertTrue(void and all(r["void"] == "lane_down" for r in void))
        s = h.summary(rows)
        self.assertEqual(s["void_rows"], len(void))
        self.assertEqual((s["alone"]["problems"], s["problems_paired"]), (0, 0), "void rows are not in any count")
        self.assertLess(len(rows), 8, "problems after the trip are not started: no row")

    def test_past_the_deadline_nothing_new_is_asked_and_finished_problems_still_count(self):
        clock = [0.0]
        def call(p):
            clock[0] += 100
            return {"text": answer("  positivity\n"), "tokens": 10}
        with mock.patch.object(h.time, "monotonic", lambda: clock[0]):
            rows, _ = h.run(self.T, lambda s, t: TARGET, call, None, lambda x: {"verdict": "accept"}, calls=1, jobs=1,
                            arms=("alone", "lessons"), lesson_block=lambda s, t, text: "## L\n", deadline=250)
        self.assertEqual(sorted((r["target"], r["arm"]) for r in rows[:2]), [("t0", "alone"), ("t0", "lessons")],
                         "t0's two arms finished (100 s each)")
        self.assertEqual(len([r for r in rows if r["target"] == "t1"]), 1, "t1's first arm started at 200 s; its second was not started")
        self.assertEqual({r["target"] for r in rows if r["target"] not in ("t0", "t1")}, set(), "nothing starts past the deadline")
        s = h.summary(rows)
        self.assertEqual((s["problems_paired"], s["alone"]["solved"], s["void_rows"]), (1, 1, 0))

    def test_a_problem_with_one_arm_void_is_not_paired(self):
        rows = [{"arm": "alone", "target": "a", "outcome": "solved", "calls": 1, "tokens": 1, "seconds": 1},
                {"arm": "lessons", "target": "a", "outcome": "failed", "calls": 1, "tokens": 1, "seconds": 1, "void": "deadline"},
                {"arm": "alone", "target": "b", "outcome": "failed", "calls": 1, "tokens": 1, "seconds": 1},
                {"arm": "lessons", "target": "b", "outcome": "solved", "calls": 1, "tokens": 1, "seconds": 1}]
        s = h.summary(rows)
        self.assertEqual((s["problems_paired"], s["only_lessons"], s["only_alone_vs_lessons"]), (1, ["b"], []))
        only_treatment = [rows[3]]                       # the lessons arm finished, its control never started
        s = h.summary(only_treatment, arms=("alone", "lessons"))
        self.assertEqual((s["problems_paired"], s["only_lessons"], s["alone"]["problems"]), (0, [], 0), "no control, no win")
        self.assertEqual(h.summary(only_treatment)["problems_paired"], 1, "without the configured arms the rows decide, as before")

    def test_every_arm_prints_a_progress_line(self):
        t = self.T[:1]
        with mock.patch("builtins.print") as p:
            h.run(t, lambda s, n: TARGET, lambda q: {"text": answer("  positivity\n"), "tokens": 10}, None,
                  lambda x: {"verdict": "accept"}, calls=1, jobs=1, arms=("alone", "lessons"), lesson_block=lambda s, n, text: "## L\n")
        lines = [c.args[0] for c in p.call_args_list if c.args]
        self.assertTrue(any(l.startswith("t0 alone: solved") for l in lines), lines)
        self.assertTrue(any(l.startswith("t0 lessons: solved") for l in lines), lines)


class Skeleton(unittest.TestCase):
    """The skeleton pilot (Burton, arXiv 2601.16172, Appendix A; Codex 20261108T152000037394Z and
    20261108T152326970171Z): the paper's fixed 16-attempt schedule against 16 unguided samples, run from a frozen
    manifest, through the router's budget gates, with no claim from an exploratory pilot."""
    T = {"target_set": "s", "target": "t1", "status": "solved", "rung": "aime"}

    def test_the_schedule_is_the_papers_16_entries_in_order(self):
        s = h.schedule()
        self.assertEqual(len(s), 16)
        self.assertEqual([k for k, _ in s[:15]], ["", "simp", "intro", "intros", "constructor", "refine ?_",
                         "refine ⟨?_, ?_⟩", "aesop", "norm_num", "linarith", "nlinarith", "ring", "ring_nf",
                         "simp\ntry aesop", "simp\ntry nlinarith"])
        self.assertEqual(s[15], ("", "Start by simplifying the goal and hypotheses using simp."))
        self.assertTrue(all(hint is None for _, hint in s[:15]))

    def test_call_i_carries_skeleton_i_and_the_arm_stops_at_the_first_accept(self):
        prompts = []
        replies = iter([answer("  nlinarith\n"), answer("  simp\n  positivity\n")])
        ask = lambda p: (prompts.append(p), next(replies))[1]
        cand, k, followed = h.skeleton(TARGET, ask, lambda t: {"verdict": "accept" if "positivity" in t else "reject"}, calls=16)
        self.assertEqual(k, 2)
        self.assertEqual(len(prompts), 2)
        self.assertNotIn("must begin", prompts[0])                     # entry 1 is the empty skeleton
        self.assertIn("```lean4\nsimp\n```", prompts[1])
        self.assertEqual(followed, 2)                                    # empty is followed by anything; call 2 began with simp

    def test_the_sixteenth_call_carries_the_hint_and_a_proof_that_ignores_its_skeleton_is_counted(self):
        prompts = []
        ask = lambda p: (prompts.append(p), answer("  positivity\n"))[1]
        cand, k, followed = h.skeleton(TARGET, ask, lambda t: {"verdict": "reject"}, calls=16)
        self.assertEqual((cand, k, len(prompts)), (None, None, 16))
        self.assertIn("Hint: Start by simplifying", prompts[15])
        self.assertEqual(followed, 2, "only the two empty-skeleton calls were followed")

    def test_the_skeleton_arm_runs_beside_alone_and_is_paired_against_it(self):
        call = lambda p: {"text": answer("  simp\n  positivity\n" if "must begin" in p else "  nlinarith\n"), "tokens": 5}
        rows, _ = h.run([self.T], lambda s, n: TARGET, call, None,
                        lambda x: {"verdict": "accept" if "positivity" in x else "reject"}, calls=16, arms=("alone", "skeleton"))
        by = {r["arm"]: r for r in rows}
        self.assertEqual((by["alone"]["outcome"], by["skeleton"]["outcome"]), ("failed", "solved"))
        self.assertEqual(by["alone"]["calls"], 16)
        self.assertEqual(by["skeleton"]["calls_to_solve"], 2)
        self.assertIn("skeleton_followed", by["skeleton"])
        s = h.summary(rows, arms=("alone", "skeleton"))
        self.assertEqual((s["only_skeleton"], s["only_alone_vs_skeleton"]), (["t1"], []))

    def test_the_router_call_sends_the_manifests_sampling_and_counts_http_requests(self):
        from utilities.kumori_api_client import KumoriAPIError
        seen = []
        def llm_chat(backend, messages, **kw):
            seen.append(kw)
            if len(seen) < 3:
                raise KumoriAPIError("per-lane RPM spacing", status_code=429, retry_after=1)
            return answer("  positivity\n"), backend, {"usage": {"completion_tokens": 9}}
        r = h.router_call("x", llm_chat, max_tokens=1024, temperature=0.6, sleep=lambda s: None)("prove it")
        self.assertEqual(r["chat_requests"], 3)
        self.assertTrue(all(k["max_tokens"] == 1024 and k["temperature"] == 0.6 for k in seen))
        m = h.Meter(lambda p: r)
        m.ask("p")
        self.assertEqual((m.calls, m.chat_requests), (1, 3), "a logical call and its chat POSTs are counted apart (f6)")

    def test_a_call_refused_locally_sends_no_request(self):
        sent = [0]
        def call(p):
            sent[0] += 1
            return {"error": "benched", "reason": "benched", "chat_requests": 1}
        rows, _ = h.run([self.T], lambda s, n: TARGET, call, None, lambda x: {"verdict": "reject"}, calls=16, jobs=1,
                        arms=("alone", "skeleton"), breaker=2)
        self.assertEqual(sent[0], 2)
        self.assertEqual(sum(r["chat_requests"] for r in rows), 2, "a breaker or deadline refusal is 0 requests (Codex r3 f6)")

    def manifest(self, **over):
        m = {"id": "skeleton-pilot-test", "kind": "exploratory pilot", "lane": "mistral-ministral-3b-2512",
             "arms": ["alone", "skeleton"], "calls": 16, "max_tokens": 1024, "temperature": 0.6,
             "top_p": "provider default, unreported", "jobs": 2, "max_minutes": 300,
             "cohort": "ledger/speed/sample-solved-2026-10-24.jsonl",
             "schedule": [[k, v] for k, v in h.schedule()], "claim": "none"}
        m.update(over)
        return m

    def test_a_manifest_must_carry_the_frozen_schedule_and_every_protocol_key(self):
        self.assertEqual(h.check_manifest(self.manifest())["calls"], 16)
        with self.assertRaises(AssertionError):
            h.check_manifest(self.manifest(schedule=[["simp", None]] * 16))
        with self.assertRaises(AssertionError):
            h.check_manifest({k: v for k, v in self.manifest().items() if k != "temperature"})
        with self.assertRaises(AssertionError):
            h.check_manifest(self.manifest(top_p=0.95))       # never a sampling value the transport does not send

    def test_the_cohort_is_the_frozen_speed_sample_not_the_rung_selection(self):
        rows = h.cohort("ledger/speed/sample-solved-2026-10-24.jsonl")
        self.assertEqual(len(rows), 45)
        self.assertTrue(all(r["status"] == "solved" for r in rows))
        self.assertIn("primer", {r["rung"] for r in rows} | {r["target_set"].split("/")[0] for r in rows})

    def test_a_preflight_refusal_is_one_void_row_and_no_claim(self):
        row = h.refused_row(self.manifest(), "lane budget: x has 10 of 100 left")
        self.assertEqual((row["void"], row["manifest"], row["claim"]), ("preflight", "skeleton-pilot-test", "none"))
        s = h.summary([row], arms=("alone", "skeleton"))
        self.assertEqual((s["problems_paired"], s["void_rows"]), (0, 1))
        s = h.refused_summary(self.manifest(), row, expected=45)
        self.assertEqual((s["complete"], s["problems_paired"], s["chat_requests"], s["claim"]), (False, 0, 0, "none"))

    def test_a_partial_run_says_it_is_incomplete(self):
        rows = [{"arm": "alone", "target": "a", "outcome": "solved", "calls": 1, "tokens": 1, "seconds": 1},
                {"arm": "skeleton", "target": "a", "outcome": "solved", "calls": 1, "tokens": 1, "seconds": 1}]
        s = h.summary(rows, arms=("alone", "skeleton"), expected=45)
        self.assertEqual((s["complete"], s["problems_paired"]), (False, 1))

    def test_main_with_a_refused_budget_writes_one_void_row_and_reports_an_incomplete_run(self):
        import io, json, tempfile, contextlib, lane_budget, relay
        from utilities import kumori_api_client as k
        out = Path(tempfile.mkdtemp()) / "run.jsonl"
        argv = ["headtohead.py", "run", "--manifest", "ledger/headtohead/manifest-skeleton-pilot-2026-11-08.json", "--out", str(out)]
        buf = io.StringIO()
        with mock.patch.object(sys, "argv", argv), mock.patch.object(k, "init", lambda *a, **kw: None), \
             mock.patch.object(relay, "fetch_json", lambda p: {"open": [], "solved": []}), \
             mock.patch.object(lane_budget, "preflight", side_effect=SystemExit("lane budget: no room")), \
             contextlib.redirect_stdout(buf):
            self.assertEqual(h.main(), 0)
        rows = [json.loads(l) for l in out.read_text().splitlines()]
        self.assertEqual([r["void"] for r in rows], ["preflight"])
        last = json.loads(buf.getvalue().strip().splitlines()[-1].split("headtohead: ", 1)[1])
        self.assertEqual((last["complete"], last["problems_paired"], last["chat_requests"]), (False, 0, 0))
