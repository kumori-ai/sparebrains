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
        tried = prompt[len(relay.RELAY):]                              # the fixed preamble names tactics too
        self.assertLess(tried.index("intro x"), tried.index("simp"))
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


class LadderDudTests(unittest.TestCase):
    """A lane that runs dry on a rung leaves the ladder on that rung only; the relay keeps it."""
    NOW = "2026-10-08T12:00:00+00:00"

    def calls(self, empty, answered, rung="math-L5", mode="ladder-x3", day="2026-10-08"):
        rows = []
        for i in range(empty + answered):
            e = i < empty
            rows.append({"backend": "b", "rung": rung, "verdict": "error" if e else "reject", "try_mode": mode,
                         "reason": "KumoriAPIError: kumori /api/v1/llm/chat HTTP 502 : unknown" if e else "type mismatch",
                         "ts": f"{day}T{i // 60:02d}:{i % 60:02d}:00+00:00"})
        return rows

    def test_dry_on_a_rung_is_out_there_and_just_under_is_in(self):
        self.assertTrue(relay.ladder_dud(self.calls(12, 8), "b", "math-L5", self.NOW))
        self.assertFalse(relay.ladder_dud(self.calls(11, 9), "b", "math-L5", self.NOW))

    def test_dry_on_one_rung_says_nothing_about_another(self):
        rows = self.calls(20, 0, rung="math-L5") + self.calls(0, 20, rung="primer")
        self.assertTrue(relay.ladder_dud(rows, "b", "math-L5", self.NOW))
        self.assertFalse(relay.ladder_dud(rows, "b", "primer", self.NOW))

    def test_too_few_calls_is_not_evidence(self):
        self.assertFalse(relay.ladder_dud(self.calls(15, 0), "b", "math-L5", self.NOW))

    def test_relay_calls_do_not_count_against_the_ladder(self):
        self.assertFalse(relay.ladder_dud(self.calls(20, 0, mode="relay"), "b", "math-L5", self.NOW))

    def test_the_bench_expires(self):
        self.assertFalse(relay.ladder_dud(self.calls(20, 0, day="2026-10-01"), "b", "math-L5", self.NOW))


def row(backend, minute, verdict="reject", mode="relay", model="m1", target="a", tset="mil"):
    return {"backend": backend, "verdict": verdict, "try_mode": mode, "model": model, "target_set": tset,
            "target": target, "ts": f"2026-10-08T10:{minute:02d}:00+00:00"}


class RealNamesInPromptTests(unittest.TestCase):
    def test_invented_names_come_with_the_closest_real_ones(self):
        d = {"target": "x", "answered": 3, "lanes_tried": 2, "unknown_names": [["Nat.Prime.dvd_pow", 5]]}
        prompt, _ = relay.relay_prompt("theorem x : True := by\n  sorry\n", d,
                                       real_names={"Nat.Prime.dvd_pow": ["Nat.Prime.dvd_of_dvd_pow"]})
        self.assertIn("`Nat.Prime.dvd_pow` does not exist; real names close to it: `Nat.Prime.dvd_of_dvd_pow`", prompt)
        bare, _ = relay.relay_prompt("theorem x : True := by\n  sorry\n", d)
        self.assertIn("`Nat.Prime.dvd_pow` does not exist", bare)


class RoundTests(unittest.TestCase):
    """A lane's three relay tries are a round; news since its last try earns another (the swarm)."""
    def test_a_round_is_spent_after_three_tries_with_no_news(self):
        prow = [row("x", m) for m in (1, 2, 3)]
        self.assertEqual(relay.tries_left(prow, "x", "m1"), 0)
        self.assertEqual(relay.tries_left(prow[:1], "x", "m1"), 2)
        self.assertEqual(relay.tries_left([], "x", "m1"), relay.RELAY_TRIES)

    def test_five_answers_by_others_open_a_new_round_and_four_do_not(self):
        mine = [row("x", m) for m in (1, 2, 3)]
        self.assertEqual(relay.tries_left(mine + [row(f"o{i}", 10 + i) for i in range(4)], "x", "m1"), 0)
        self.assertEqual(relay.tries_left(mine + [row(f"o{i}", 10 + i) for i in range(5)], "x", "m1"), relay.RELAY_TRIES)

    def test_others_errors_are_not_news(self):
        prow = [row("x", m) for m in (1, 2, 3)] + [row(f"o{i}", 10 + i, verdict="error") for i in range(9)]
        self.assertEqual(relay.tries_left(prow, "x", "m1"), 0)

    def test_a_persons_comment_opens_a_new_round(self):
        prow = [row("x", m) for m in (1, 2, 3)]
        self.assertEqual(relay.tries_left(prow, "x", "m1", ["2026-10-08T10:30:00+00:00"]), relay.RELAY_TRIES)
        self.assertEqual(relay.tries_left(prow, "x", "m1", ["2026-10-08T09:00:00+00:00"]), 0, "an older comment was already read")

    def test_a_new_model_behind_the_lane_opens_a_new_round(self):
        prow = [row("x", m) for m in (1, 2, 3)]
        self.assertEqual(relay.tries_left(prow, "x", "m2"), relay.RELAY_TRIES)

    def test_the_round_counts_only_tries_since_the_last_news(self):
        prow = ([row("x", m) for m in (1, 2, 3)] + [row(f"o{i}", 10 + i) for i in range(5)] + [row("x", 20)])
        self.assertEqual(relay.tries_left(prow, "x", "m1"), 2)


class NextProblemTests(unittest.TestCase):
    LANES = [dict(backend="x", model="m1"), dict(backend="y", model="m1")]

    def opens(self, *names):
        return [dict(target_set="mil", target=n, order=i) for i, n in enumerate(names)]

    def test_breadth_first_fewest_relay_tries_then_order(self):
        by = relay.problem_rows([row("x", 1, target="a"), row("x", 2, target="b"), row("y", 3, target="b")])
        self.assertEqual(relay.next_problem(self.opens("a", "b", "c"), self.LANES, by), ("mil", "c"))
        self.assertEqual(relay.next_problem(self.opens("a", "b"), self.LANES, by), ("mil", "a"))

    def test_a_fresh_comment_jumps_the_queue(self):
        by = relay.problem_rows([row("x", m, target="b") for m in (1, 2, 3)])
        people = {("mil", "b"): ["2026-10-08T10:30:00+00:00"]}
        self.assertEqual(relay.next_problem(self.opens("a", "b"), self.LANES, by, people), ("mil", "b"))

    def test_nothing_owed_is_none(self):
        by = relay.problem_rows([row(b, m, target="a") for b, ms in (("x", (1, 2, 3)), ("y", (4, 5, 6))) for m in ms])
        self.assertIsNone(relay.next_problem(self.opens("a"), self.LANES, by))

    def test_a_problem_rests_at_the_ceiling_until_a_person_speaks(self):
        rows = [dict(row(f"l{i % 9}", 0), ts=f"2026-10-08T{(i // 60):02d}:{i % 60:02d}:00+00:00")
                for i in range(relay.PROBLEM_CEILING)]
        prow = relay.problem_rows(rows)[("mil", "a")]
        self.assertTrue(relay.resting(prow))
        self.assertFalse(relay.resting(prow, ["2026-10-08T23:00:00+00:00"]))


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
