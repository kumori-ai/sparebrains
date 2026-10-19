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

    def test_each_lane_skips_only_the_goals_it_tried_itself(self):
        rows = [{"sha": "a"}, {"sha": "b", "backend": "groq-gptoss-decompose"}]
        self.assertEqual(decompose.tried_by(rows, decompose.LANE["backend"]), {"a"})     # old rows are Leanstral's
        self.assertEqual(decompose.tried_by(rows, "groq-gptoss-decompose"), {"b"})

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

    def test_a_lane_names_its_rows_and_tries(self):
        lane = decompose.lane_of("groq-gptoss")
        self.assertEqual((lane["backend"], lane["mode"], lane["file"]), ("groq-gptoss-decompose", "goal-closer", "decompose"))
        self.assertIs(decompose.lane_of(None), decompose.LANE)

if __name__ == "__main__":
    unittest.main()
