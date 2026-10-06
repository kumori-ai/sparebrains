"""Stage-2 relay contracts (no LLM calls, no network): what a relay prompt may carry, how its
rows are labeled, and that relay rows never close a ladder cell."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import relay
from attempt import owed_history
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

    def test_a_comment_makes_it_relay_plus_thread(self):
        c = dict(comment_id=7, author="someone", body="try induction on n")
        prompt, meta = relay.relay_prompt(TARGET, dossier(thread=[c]))
        self.assertEqual((meta["try_mode"], meta["comment_ids"]), ("relay+thread", [7]))
        self.assertIn("try induction on n", prompt)

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


class RelayLedgerTests(unittest.TestCase):
    def ledger(self, rows):
        root = Path(tempfile.mkdtemp())
        (root / "mil").mkdir()
        (root / "mil" / "1.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
        return root

    def test_relay_rows_never_close_a_ladder_cell(self):
        rows = [dict(target_set="mil", target="t", backend="b", verdict="reject", try_mode=m, ts="2026-10-06T00:00:00+00:00")
                for m in ("cold", "relay", "relay+thread", "relay")]
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
