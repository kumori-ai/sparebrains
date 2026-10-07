"""Stage-2 relay contracts (no LLM calls, no network): what a relay prompt may carry, how its
rows are labeled, and that relay rows never close a ladder cell."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import relay
from attempt import owed_history, extract_proof, align_tactics
from ladder import RUNGS

TARGET = "import Mathlib\n\ntheorem t (n : ℕ) : n = n := by\n  sorry\n"


def dossier(**kw):
    d = dict(target_set="mil", target="t", solved=False, answered=94, lanes_tried=36,
             failures=[dict(kind="unknown_name", n=48, lanes=21), dict(kind="unsolved_goals", n=11, lanes=7)],
             unknown_names=[["Nat.fake", 3], ["h", 9]],
             near_misses=[dict(id=101, backend="lane-a", failure_kind="unsolved_goals", proof="  intro x", lean_output="unsolved goals"),
                          dict(id=102, backend="lane-b", failure_kind="tactic_failed", proof="  simp", lean_output="simp failed")],
             thread=[])
    d.update(kw)
    return d


class RelayPromptTests(unittest.TestCase):
    def test_a_solved_problem_is_refused(self):
        with self.assertRaises(ValueError):
            relay.relay_prompt(TARGET, dossier(solved=True, near_misses=[]))

    def test_dossier_alone_is_relay_and_points_at_the_best_near_miss(self):
        prompt, meta = relay.relay_prompt(TARGET, dossier())
        self.assertEqual(meta["try_mode"], "relay")
        self.assertEqual(meta["prev_id"], 101)
        self.assertIn("Nat.fake", prompt)
        self.assertNotIn(", h\n", prompt + "\n")                       # a local name is not a missing library name
        self.assertLess(prompt.index("intro x"), prompt.index("simp"))
        self.assertTrue(prompt.endswith(TARGET))

    def test_the_proof_only_answer_it_asks_for_is_one_the_extractor_takes(self):
        prompt, _ = relay.relay_prompt(TARGET, dossier())
        self.assertIn("only the proof that replaces `sorry`", prompt)
        self.assertEqual(extract_proof("```lean\nintro x\nsimp\n```", "t"), "  intro x\n  simp\n")

    def test_a_comment_makes_it_relay_plus_thread(self):
        c = dict(comment_id=7, author="someone", body="try induction on n")
        prompt, meta = relay.relay_prompt(TARGET, dossier(thread=[c]))
        self.assertEqual((meta["try_mode"], meta["comment_ids"]), ("relay+thread", [7]))
        self.assertIn("try induction on n", prompt)

    def test_the_bots_own_digests_are_not_the_thread(self):
        bot = dict(comment_id=8, author="kumori-ai[bot]", author_type="Bot", body="Relay run 1: 5 calls")
        prompt, meta = relay.relay_prompt(TARGET, dossier(thread=[bot]))
        self.assertEqual(meta["try_mode"], "relay")
        self.assertNotIn("Relay run 1", prompt)

    def test_this_jobs_rejects_come_first(self):
        prompt, meta = relay.relay_prompt(TARGET, dossier(), [("lane-z", "type_mismatch", "  exact rfl_new", "mismatch")])
        self.assertLess(prompt.index("exact rfl_new"), prompt.index("intro x"))
        self.assertEqual(meta["prev_id"], 101)          # this job's own row has no site id yet

    def test_the_cap_never_cuts_the_target_file(self):
        huge = [dict(id=i, backend="b", failure_kind="unsolved_goals", proof="x" * 50_000, lean_output="y" * 50_000)
                for i in range(5)]
        prompt, _ = relay.relay_prompt(TARGET, dossier(near_misses=huge, thread=[dict(body="z" * 90_000)] * 20))
        self.assertLessEqual(len(prompt), relay.PROMPT_CAP + len(TARGET))
        self.assertTrue(prompt.endswith(TARGET))


class DossierFetchTests(unittest.TestCase):
    def test_the_fetch_names_itself(self):
        seen = {}
        class Reply:
            def __enter__(self): return self
            def __exit__(self, *a): return False
            def read(self): return b'{"target": "t"}'
        def fake_urlopen(req, timeout):
            seen["ua"] = req.get_header("User-agent")
            return Reply()
        orig = relay.urllib.request.urlopen
        relay.urllib.request.urlopen = fake_urlopen
        try:
            self.assertEqual(relay.fetch_dossier("mil", "t"), {"target": "t"})
        finally:
            relay.urllib.request.urlopen = orig
        self.assertEqual(seen["ua"], relay.USER_AGENT)       # Cloudflare 403s the default Python-urllib agent


class NextProblemTests(unittest.TestCase):
    def test_walks_the_order_past_problems_whose_tries_are_spent(self):
        from collections import defaultdict
        tried = defaultdict(lambda: {"answered": 0, "errors": 0})
        tried[("mil", "a", "x")] = {"answered": 3, "errors": 0}
        tried[("mil", "a", "y")] = {"answered": 0, "errors": 0, "router_errors": 3}   # three empty calls spend it
        open_list = [dict(target_set="mil", target="b", order=2), dict(target_set="mil", target="a", order=1)]
        lanes = [dict(backend="x"), dict(backend="y")]
        self.assertEqual(relay.next_problem(open_list, lanes, tried), ("mil", "b"))
        tried[("mil", "b", "x")] = tried[("mil", "b", "y")] = {"answered": 3, "errors": 0}
        self.assertIsNone(relay.next_problem(open_list, lanes, tried))


class TokenBudgetTests(unittest.TestCase):
    def test_thinking_models_get_room_in_every_mode(self):
        from attempt import lane_max_tokens
        self.assertEqual(lane_max_tokens({"capability": {"is_reasoning_model": True}}, 4000), relay.MAX_TOKENS)
        self.assertEqual(lane_max_tokens({"capability": {"is_reasoning_model": False}}, 4000), 4000)
        self.assertEqual(lane_max_tokens({}, 4000), 4000)
        self.assertEqual(lane_max_tokens({"capability": {"is_reasoning_model": True}}, 20000), 20000)

    def test_thinking_models_are_asked_for_medium_effort(self):
        from attempt import lane_effort
        self.assertEqual(lane_effort({"capability": {"is_reasoning_model": True}}), "medium")
        self.assertIsNone(lane_effort({"capability": {}}))


class EmptyLaneTests(unittest.TestCase):
    EMPTY = "KumoriAPIError: kumori /api/v1/llm/chat HTTP 502 : unknown"

    def rows(self, b, verdicts, mode="relay", day="2026-10-07"):
        return [dict(backend=b, verdict=v, try_mode=mode, ts=f"{day}T{10 + i:02d}:00:00+00:00",
                     reason=self.EMPTY if v == "error" else "lean exit 1") for i, v in enumerate(verdicts)]

    def test_running_dry_needs_ten_calls_mostly_empty(self):
        self.assertTrue(relay.running_dry(self.rows("d", ["error"] * 6 + ["reject"] * 4), "d"))
        self.assertFalse(relay.running_dry(self.rows("d", ["error"] * 5 + ["reject"] * 5), "d"))
        self.assertFalse(relay.running_dry(self.rows("d", ["error"] * 9), "d"))          # not enough calls to judge

    def test_relay_bench_needs_six_empty_relay_calls_and_expires(self):
        rows = self.rows("d", ["error"] * 6)
        self.assertTrue(relay.relay_benched(rows, "d", "2026-10-08T00:00:00+00:00"))
        self.assertFalse(relay.relay_benched(rows, "d", "2026-10-11T00:00:00+00:00"))   # three days on, back in
        self.assertFalse(relay.relay_benched(self.rows("d", ["error"] * 5 + ["reject"]), "d", "2026-10-08T00:00:00+00:00"))
        self.assertFalse(relay.relay_benched(self.rows("d", ["error"] * 6, mode="cold"), "d", "2026-10-08T00:00:00+00:00"))

    def test_a_dry_thinking_model_is_asked_for_low_effort(self):
        import attempt
        attempt.RUNNING_DRY.add("dry-lane")
        try:
            self.assertEqual(attempt.lane_effort({"backend": "dry-lane", "capability": {"is_reasoning_model": True}}), "low")
            self.assertEqual(attempt.lane_effort({"backend": "ok-lane", "capability": {"is_reasoning_model": True}}), "medium")
        finally:
            attempt.RUNNING_DRY.discard("dry-lane")


class LayoutTests(unittest.TestCase):
    def test_the_first_line_shallower_than_the_rest_is_aligned(self):
        # #47356's shape (2026-10-06): Lean stopped at "unexpected token 'have'" before any math
        broken = ["  intro h", "    have hp : p ∣ m := by", "      exact x", "    exact y"]
        self.assertEqual(align_tactics(broken), ["  intro h", "  have hp : p ∣ m := by", "    exact x", "  exact y"])

    def test_a_block_opener_keeps_its_body_nested(self):
        lines = ["  have a : 1 = 1 := by", "    rfl"]
        self.assertEqual(align_tactics(lines), lines)
        self.assertEqual(align_tactics(["  refine ⟨_, ?_⟩ <;>", "    simp"]), ["  refine ⟨_, ?_⟩ <;>", "    simp"])

    def test_extraction_applies_it(self):
        self.assertEqual(extract_proof("```lean\nintro h\n  exact h\n```", "t"), "  intro h\n  exact h\n")


class RelayLedgerTests(unittest.TestCase):
    def ledger(self, rows):
        root = Path(tempfile.mkdtemp())
        (root / "mil").mkdir()
        (root / "mil" / "1.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
        return root

    def test_relay_rows_never_close_a_ladder_cell(self):
        rows = [dict(target_set="mil", target="t", backend="b", verdict="reject", try_mode=m, ts="2026-10-06T00:00:00+00:00")
                for m in ("cold", "relay", "relay+thread", "relay", "fixer")]
        root = self.ledger(rows)
        self.assertEqual(owed_history(root)[("mil", "t", "b")]["answered"], 1)
        self.assertEqual(owed_history(root, relay_rows=True)[("mil", "t", "b")]["answered"], 3)

    def test_strength_counts_distinct_hard_targets_and_skips_lanes_with_none(self):
        rows = [dict(backend="a", target_set="m", target="x", rung="amc12", verdict="accept"),
                dict(backend="a", target_set="m", target="x", rung="amc12", verdict="accept"),
                dict(backend="a", target_set="m", target="y", rung="math-L1", verdict="accept"),
                dict(backend="b", target_set="m", target="z", rung="imo", verdict="reject")]
        strength = relay.lane_strength(rows, RUNGS)
        self.assertEqual(strength["a"], 1)
        lanes = [dict(backend="a"), dict(backend="b")]
        self.assertEqual([l["backend"] for l in relay.strongest(lanes, strength, 5)], ["a"])


if __name__ == "__main__":
    unittest.main()
