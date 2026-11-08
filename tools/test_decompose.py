"""Decomposition (tools/decompose.py): a stand-in model and judge, and subgoals.repair stood in where it takes a
proof apart, so these test the recursion, not Lean."""
import sys, unittest
from pathlib import Path
from unittest import mock

sys.path[:0] = [str(Path(__file__).resolve().parent)]
import decompose, subgoals

PREFIX = "import Mathlib\n\ntheorem t (x : ℝ) : x = x := by"
GOAL = "theorem sb_goal (x : ℝ) (h : 0 < x) : 0 < x ^ 2 := by"
STEP = "theorem sb_goal (x : ℝ) (h : 0 < x) : x ^ 2 = x * x := by"


def reply(body):
    return f"```lean4\n{GOAL}\n{body}```"


class Decompose(unittest.TestCase):
    def test_a_proof_the_kernel_accepts_comes_back_as_the_body(self):
        log = []
        body = decompose.decompose(GOAL, PREFIX, ask=lambda p: reply("  positivity\n"), run_lean=None,
                                   judge_text=lambda t: {"verdict": "accept"}, log=log)
        self.assertEqual(body.strip(), "positivity")
        self.assertEqual(log, [{"depth": decompose.DEPTH, "outcome": "proved"}])

    def test_an_open_step_goes_one_level_down_and_its_proof_is_spliced(self):
        head = decompose.lemma_prefix(PREFIX, GOAL)
        sketch = head + "  have h2 : x ^ 2 = x * x := by\n    sorry\n  positivity\n"
        asks = []
        def ask(p):
            asks.append(p)
            return reply("  have h2 : x ^ 2 = x * x := by\n    ring_nf\n  positivity\n") if len(asks) == 1 else \
                f"```lean4\n{STEP}\n  ring\n```"
        judge = lambda t: {"verdict": "accept" if ("    ring\n" in t or t.rstrip().endswith("ring")) else "reject",
                           "output": "x.lean:5:4: error: ring_nf failed"}
        with mock.patch.object(subgoals, "repair", return_value={"sketch": sketch, "goals": [STEP]}):
            body = decompose.decompose(GOAL, PREFIX, ask=ask, run_lean=None, judge_text=judge)
        self.assertEqual(len(asks), 2)
        self.assertIn(STEP, asks[1])                        # the open step was asked as its own goal
        self.assertIn("    ring\n", body)
        self.assertNotIn("sorry", body)

    def test_one_unproved_step_leaves_the_goal_unproved(self):
        head = decompose.lemma_prefix(PREFIX, GOAL)
        sketch = head + "  have h2 : x ^ 2 = x * x := by\n    sorry\n  positivity\n"
        judge = lambda t: {"verdict": "reject", "output": "x.lean:5:4: error: failed"}
        with mock.patch.object(subgoals, "repair", return_value={"sketch": sketch, "goals": [STEP]}):
            body = decompose.decompose(GOAL, PREFIX, ask=lambda p: reply("  nlinarith\n"), run_lean=None,
                                       judge_text=judge, depth=1)
        self.assertIsNone(body)

    def test_the_ask_budget_caps_every_level_together(self):
        head = decompose.lemma_prefix(PREFIX, GOAL)
        sketch = head + "  have h2 : x ^ 2 = x * x := by\n    sorry\n  positivity\n"
        asks = []
        ask = lambda p: (asks.append(p), reply("  nlinarith\n"))[1]
        with mock.patch.object(subgoals, "repair", return_value={"sketch": sketch, "goals": [STEP]}):
            decompose.decompose(GOAL, PREFIX, ask=ask, run_lean=None,
                                judge_text=lambda t: {"verdict": "reject", "output": ""}, depth=50)
        self.assertEqual(len(asks), decompose.MAX_ASKS)

    def test_a_level_that_cannot_be_taken_apart_is_asked_once_more_with_leans_error(self):
        asks = []
        ask = lambda p: (asks.append(p), reply("  nlinarith\n"))[1]
        judge = lambda t: {"verdict": "reject", "output": "x.lean:4:2: error: linarith failed to find a contradiction"}
        with mock.patch.object(subgoals, "repair", return_value={"stopped": "15 failing steps: not close"}):
            self.assertIsNone(decompose.decompose(GOAL, PREFIX, ask=ask, run_lean=None, judge_text=judge))
        self.assertEqual(len(asks), 2)                      # once, then once with the error; never a loop
        self.assertIn("linarith failed", asks[1])

    def test_a_failed_call_says_why_in_the_log(self):
        log = []
        decompose.decompose(GOAL, PREFIX, ask=lambda p: {"error": "RuntimeError: HTTP 429"}, run_lean=None,
                            judge_text=lambda t: {"verdict": "accept"}, log=log)
        self.assertEqual(log[0]["stopped"], "no answer: RuntimeError: HTTP 429")

    def test_no_answer_is_no_proof(self):
        self.assertIsNone(decompose.decompose(GOAL, PREFIX, ask=lambda p: None, run_lean=None,
                                              judge_text=lambda t: {"verdict": "accept"}))



class RouterLane(unittest.TestCase):
    """Any lane can do the asking (charter: every tool runs on any lane); Leanstral stays the default."""

    def test_each_goals_row_is_handed_over_as_soon_as_it_is_done(self):
        from unittest import mock
        goals = [{"sha": s, "target_set": "minif2f/test", "target": "t", "goal": "theorem sb_goal : True := by\n  sorry"}
                 for s in ("a", "b")]
        seen = []
        with mock.patch.object(decompose, "decompose", return_value=None):
            rows, solves = decompose.run(goals, lambda s, t: "theorem t : True := by\n  sorry", ask=None, run_lean=None,
                                         judge_text=None, jobs=1, on_row=lambda r: seen.append(r["sha"]))
        self.assertEqual(seen, ["a", "b"], "each row arrives before the run ends, so a timeout loses none")
        self.assertEqual([r["sha"] for r in rows], ["a", "b"])

    def run_one_with_close(self, close_result):
        goals = [{"sha": "a", "target_set": "minif2f/test", "target": "t", "goal": "theorem sb_goal : True := by\n  sorry"}]
        with mock.patch.object(decompose, "decompose", return_value="  trivial\n"), \
                mock.patch.object(decompose.goal_closer, "close", return_value=close_result):
            rows, solves = decompose.run(goals, lambda s, t: "theorem t : True := by\n  sorry", ask=None, run_lean=None,
                                         judge_text=None, jobs=1)
        return rows[0], solves

    def test_a_proved_goal_that_does_not_splice_keeps_its_body_and_why(self):
        # 2026-11-05: imo_1974_p3's goal was proved 10-21 and its body was lost; the row said only 'splice failed'
        row, solves = self.run_one_with_close({"verdict": "reject", "stage": "splice", "output": "no sketch had exactly one hole"})
        self.assertEqual(row["outcome"], "goal proved, splice failed")
        self.assertEqual(row["stage"], "splice")
        self.assertEqual(row["body"], "  trivial\n", "the proof of the goal is kept for a later splice")
        self.assertIn("exactly one hole", row["splice_output"])
        self.assertEqual(solves, [])

    def test_a_body_lean_rejects_alone_is_a_failure_not_a_proved_goal(self):
        row, _ = self.run_one_with_close({"verdict": "reject", "stage": "goal", "output": "unsolved goals"})
        self.assertEqual(row["outcome"], "failed")
        self.assertNotIn("body", row)

    def test_a_solve_keeps_its_body_in_the_row(self):
        # 2026-11-05 run 42061251877: mathd_numbertheory_495 and _711 were kernel-accepted at 16:23 and 16:58, the step
        # hit its 310 min cap before the end-of-run publish, and with no body in the rows both proofs were lost
        row, solves = self.run_one_with_close({"verdict": "accept", "stage": "problem", "candidate": "c", "output": ""})
        self.assertEqual(row["outcome"], "solved")
        self.assertEqual(row["body"], "  trivial\n")
        self.assertEqual((row["goal"], row["sketches"]), ("theorem sb_goal : True := by\n  sorry", []),
                         "the row alone can publish it later")
        self.assertEqual(len(solves), 1)

    def test_a_solved_goal_is_not_tried_so_a_lost_solve_is_asked_again(self):
        rows = [{"sha": "s", "outcome": "solved", "levels": [{"outcome": "proved"}]},
                {"sha": "f", "outcome": "failed", "levels": [{"outcome": "x"}]}]
        self.assertEqual(decompose.tried_by(rows, decompose.LANE["backend"]), {"f"})
        rows.insert(0, {"sha": "s", "outcome": "failed", "levels": [{"outcome": "x"}]})   # Codex f3: a solve wins
        self.assertEqual(decompose.tried_by(rows, decompose.LANE["backend"]), {"f"})

    def test_a_solve_on_a_goal_outside_the_stored_queue_still_publishes(self):   # Codex f2: the temp queue is gone
        rows = [{"sha": "s", "target_set": "minif2f/test", "target": "t", "outcome": "solved", "body": "  trivial\n",
                 "goal": "theorem sb_goal : True := by", "sketches": ["x"]}]
        seen = {}
        def judge_goals(answers, prover_rows, goals, **kw):
            seen.update(goals=goals)
            return {"accept": 1}
        self.assertEqual(decompose.publish_rows(rows, {}, judge_goals=judge_goals, prover_rows=[], judge_text=None,
                                                record=None, lane=decompose.LANE), {"accept": 1})
        self.assertEqual(seen["goals"]["s"]["sketches"], ["x"])

    def test_publish_takes_the_lane_the_rows_were_written_under(self):
        self.assertEqual(decompose.lane_from_rows([{"backend": decompose.LANE["backend"]}], "auto"), decompose.LANE)
        self.assertEqual(decompose.lane_from_rows([{"backend": "groq-x-decompose"}], "auto")["model"], "groq-x")

    def test_publish_rebuilds_the_solves_from_the_rows(self):
        goal = {"sha": "s", "target_set": "minif2f/test", "target": "t", "goal": "theorem sb_goal : True := by", "sketches": ["x"]}
        rows = [{"sha": "s", "target_set": "minif2f/test", "target": "t", "outcome": "solved", "body": "  trivial\n"},
                {"sha": "f", "target_set": "minif2f/test", "target": "u", "outcome": "failed"},
                {"sha": "lost", "target_set": "minif2f/test", "target": "v", "outcome": "solved"}]   # no body: nothing to publish
        seen = {}
        def judge_goals(answers, prover_rows, goals, **kw):
            seen.update(answers=answers, goals=goals)
            return {"accept": len(answers)}
        out = decompose.publish_rows(rows, {"s": goal}, judge_goals=judge_goals, prover_rows=[], judge_text=None,
                                     record=None, lane=decompose.LANE)
        self.assertEqual(out, {"accept": 1})
        self.assertEqual([a["goal"] for a in seen["answers"]], ["s"])
        self.assertIn("  trivial", seen["answers"][0]["text"])
        self.assertEqual(list(seen["goals"]), ["s"])

    def test_reachable_problems_go_first_and_the_bar_joins_only_when_allowed(self):
        q = [{"sha": s, "target_set": "minif2f/test", "target": t, "file_ok": True}
             for s, t in (("g1", "imo_a"), ("g2", "amc_b"), ("g3", "imo_c"), ("g4", "imo_a"))]
        rung = {("minif2f/test", "imo_a"): "imo", ("minif2f/test", "amc_b"): "amc12", ("minif2f/test", "imo_c"): "imo"}
        reach = {("minif2f/test", "imo_c"), ("minif2f/test", "amc_b")}
        pick = lambda bar: [g["sha"] for g in decompose.pick_goals(q, rung, {"g4"}, reach, bar, 10)]
        self.assertEqual(pick(False), ["g3", "g1"], "bar problem out, reachable first, a tried goal skipped")
        self.assertEqual(pick(True), ["g2", "g3", "g1"])

    def test_a_lost_solve_goes_first(self):
        """#642: run 42124394793 left the 4 goals whose solves were lost outside its first 25 (reachable first won)."""
        q = [{"sha": s, "target_set": "minif2f/test", "target": t, "file_ok": True}
             for s, t in (("r1", "imo_c"), ("lost", "imo_a"), ("r2", "imo_c"))]
        rung = {("minif2f/test", "imo_a"): "imo", ("minif2f/test", "imo_c"): "imo"}
        got = [g["sha"] for g in decompose.pick_goals(q, rung, set(), {("minif2f/test", "imo_c")}, True, 2, first={"lost"})]
        self.assertEqual(got, ["lost", "r1"])
        rows = [{"sha": "lost", "outcome": "solved"}, {"sha": "x", "outcome": "failed"}, {"sha": "o", "outcome": "solved", "backend": "other"}]
        self.assertEqual(decompose.solved_by(rows, decompose.LANE["backend"]), {"lost"})

    def test_a_goal_restating_its_theorem_goes_last(self):
        q = [{"sha": "r", "target_set": "minif2f/test", "target": "imo_c", "file_ok": True, "restates": True},
             {"sha": "s", "target_set": "minif2f/test", "target": "imo_a", "file_ok": True}]
        rung = {("minif2f/test", "imo_a"): "imo", ("minif2f/test", "imo_c"): "imo"}
        got = [g["sha"] for g in decompose.pick_goals(q, rung, set(), {("minif2f/test", "imo_c")}, True, 10)]
        self.assertEqual(got, ["s", "r"], "a real step first, though only the restating goal's problem is reachable")

    def test_a_goal_cut_at_the_cap_twice_is_asked_with_effort_none(self):
        cut = {"stopped": "no answer: empty reply (finish=length, 120000 tokens)"}
        rows = [{"sha": "a", "levels": [cut, cut]}, {"sha": "b", "levels": [cut]},
                {"sha": "c", "levels": [cut], "backend": "other-decompose"}, {"sha": "c", "levels": [cut]}]
        self.assertEqual(decompose.cut_at_cap(rows, decompose.LANE["backend"]), {"a"})
        old = {"stopped": "no answer: empty reply (finish=length, 40000 tokens)"}
        self.assertEqual(decompose.cut_at_cap([{"sha": "m", "levels": [old, cut]}], decompose.LANE["backend"]), set(),
                         "a cut at an older, smaller cap does not count (imo_1977_p6: one 40k, one 120k)")
        seen = []
        ask = lambda p, effort=None: seen.append(effort) or None
        goals = [{"sha": s, "target_set": "minif2f/test", "target": "t", "goal": "theorem sb_goal : True := by\n  sorry"}
                 for s in ("a", "b")]
        rows, _ = decompose.run(goals, lambda s, t: "theorem t : True := by\n  sorry", ask, None, None, jobs=1,
                                effort_of=lambda g: "none" if g["sha"] == "a" else None)
        self.assertEqual([r["effort"] for r in rows], ["none", None])
        self.assertEqual(seen, ["none", None], "the effort reaches the ask")

    def test_each_lane_skips_only_the_goals_it_tried_itself(self):
        rows = [{"sha": "a"}, {"sha": "b", "backend": "groq-gptoss-decompose"}]
        self.assertEqual(decompose.tried_by(rows, decompose.LANE["backend"]), {"a"})     # old rows are Leanstral's
        self.assertEqual(decompose.tried_by(rows, "groq-gptoss-decompose"), {"b"})

    def test_a_goal_that_never_got_an_answer_was_not_tried(self):
        blank = {"sha": "a", "levels": [{"depth": 2, "stopped": "no answer: empty reply (finish=length, 40000 tokens)"},
                                        {"depth": 2, "stopped": "no answer: HTTP 503"}]}
        answered = {"sha": "b", "levels": [{"depth": 2, "stopped": "no answer"}, {"depth": 2, "steps_left": 1}]}
        self.assertEqual(decompose.tried_by([blank, answered], decompose.LANE["backend"]), {"b"})

    def test_a_router_lane_waits_out_its_pacing_then_says_why_it_gave_up(self):
        class Err(Exception):
            retry_after = 0.01
        calls = []
        def chat(backend, messages, **kw):
            calls.append(backend)
            if len(calls) == 1:
                raise Err("per-lane RPM spacing")
            return "```lean4\nx\n```", {}, {}
        ask, _ = decompose.router_ask("groq-gptoss", chat=chat)
        self.assertEqual(ask("p"), "```lean4\nx\n```")
        self.assertEqual(calls, ["groq-gptoss", "groq-gptoss"])
        bad, _ = decompose.router_ask("groq-gptoss", chat=lambda *a, **k: (_ for _ in ()).throw(RuntimeError("HTTP 503")))
        self.assertEqual(bad("p"), {"error": "RuntimeError: HTTP 503"})

    def test_auto_takes_the_strongest_live_lane_that_is_not_failing(self):
        hard = lambda b, t: {"backend": b, "verdict": "accept", "rung": "aime", "target_set": "s", "target": t,
                             "ts": "2026-10-19T00:00:00+00:00"}
        rows = [hard("a", "x"), hard("a", "y"), hard("b", "x")]
        live = [{"backend": "a", "provider": "p"}, {"backend": "b", "provider": "q"}, {"backend": "c", "provider": "r"}]
        self.assertEqual(decompose.pick_lane(live, rows, "2026-10-19T12:00:00+00:00")["backend"], "a")
        self.assertEqual(decompose.pick_lane(live[1:], rows, "2026-10-19T12:00:00+00:00")["backend"], "b")
        self.assertIsNone(decompose.pick_lane(live[2:], rows, "2026-10-19T12:00:00+00:00"), "no hard solve, no lane")

    def test_a_lane_names_its_rows_and_tries(self):
        lane = decompose.lane_of("groq-gptoss")
        self.assertEqual((lane["backend"], lane["mode"], lane["file"]), ("groq-gptoss-decompose", "goal-closer", "decompose"))
        self.assertIs(decompose.lane_of(None), decompose.LANE)


class WorkflowBudget(unittest.TestCase):
    def test_the_steps_leave_room_to_publish_inside_the_job(self):
        # Codex 20261105 refresh f3: refresh 90 + decompose 310 could exceed the job's 340, and a job timeout cancels the
        # publish step too, losing every row; GitHub docs, jobs.<job_id>.timeout-minutes
        import yaml
        wf = yaml.safe_load((Path(__file__).resolve().parent.parent / ".github" / "workflows" / "decompose.yml").read_text())
        job = wf["jobs"]["decompose"]
        capped = {st["name"]: st.get("timeout-minutes") for st in job["steps"] if "name" in st}
        for name in ("lean + mathlib cache + build", "decompose", "publish the ledger"):
            self.assertTrue(capped.get(name), f"{name} has no timeout of its own (Codex f4)")
        self.assertTrue(capped.get("publish the solves"), "solves publish in a step of their own, after a timeout too")
        self.assertLessEqual(sum(t for t in capped.values() if t) + 5, job["timeout-minutes"],
                             "every capped step at its limit still ends before the job does")


if __name__ == "__main__":
    unittest.main()
