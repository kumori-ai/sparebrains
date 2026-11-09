"""tools/stall.py: a problem is stalled when it is open and nothing kernel-verified has happened on it for DAYS days.
Progress is an accepted solve or a new distinct verified lemma; a reject's error position is never progress (Codex
20261109T204513251417Z f3: the same failing proof with blank lines added moved its first error 20 lines)."""
import sys
import unittest
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import stall

NOW = datetime(2026, 11, 9, 12, 0, tzinfo=timezone.utc)
OPEN = {("minif2f/test", "imo_1985_p6"), ("minif2f/test", "amc12a_2020_p4")}


def row(ts, target, verdict, mode="cold", backend="lane-a", **kw):
    return {"ts": ts, "target_set": "minif2f/test", "target": target, "verdict": verdict, "try_mode": mode,
            "backend": backend, "rung": "imo", **kw}


class Stalled(unittest.TestCase):
    def test_an_open_problem_with_no_verified_progress_for_days_is_stalled_and_ranked_by_idle_time(self):
        rows = [row("2026-10-01T00:00:00+00:00", "imo_1985_p6", "reject"),
                row("2026-11-01T00:00:00+00:00", "imo_1985_p6", "reject", backend="lane-b"),
                row("2026-10-20T00:00:00+00:00", "amc12a_2020_p4", "reject"),
                row("2026-11-08T00:00:00+00:00", "amc12a_2020_p4", "lemma-accept", mode="lemma-queue-step", lemma="x > 0")]
        s = stall.stalled(rows, OPEN, NOW, days=14)
        self.assertEqual([x["target"] for x in s], ["imo_1985_p6"])
        self.assertEqual(s[0]["idle_days"], 39, "idle since the first try when nothing was ever verified")
        self.assertEqual(s[0]["tries"], 2)
        self.assertEqual(s[0]["lanes"], 2)
        self.assertEqual(s[0]["paths"], {"cold": 2})
        self.assertIsNone(s[0]["last_progress"])

    def test_a_verified_lemma_or_a_solve_resets_the_clock_a_later_error_line_does_not(self):
        imo = {("minif2f/test", "imo_1985_p6")}
        rows = [row("2026-10-01T00:00:00+00:00", "imo_1985_p6", "reject", reason="lean exit 1: 8:2: error: x"),
                row("2026-11-08T00:00:00+00:00", "imo_1985_p6", "reject", reason="lean exit 1: 28:2: error: x")]
        self.assertEqual(stall.stalled(rows, imo, NOW)[0]["idle_days"], 39)
        rows.append(row("2026-11-05T00:00:00+00:00", "imo_1985_p6", "lemma-accept", mode="relay-subgoal", lemma="a ≤ b"))
        self.assertEqual(stall.stalled(rows, imo, NOW), [], "4 days since a verified lemma is not a stall")
        self.assertEqual(stall.stalled(rows, imo, NOW, days=3)[0]["last_progress"], "2026-11-05T00:00:00+00:00")

    def test_the_same_lemma_verified_twice_is_one_event_distinct_lemmas_sharing_a_600_char_prefix_are_two(self):
        long = "p" * 600
        rows = [row("2026-10-01T00:00:00+00:00", "imo_1985_p6", "lemma-accept", mode="relay-subgoal", lemma="a ≤ b"),
                row("2026-11-07T00:00:00+00:00", "imo_1985_p6", "lemma-accept", mode="relay-subgoal", lemma="a ≤ b")]
        self.assertEqual(stall.progress(rows)[("minif2f/test", "imo_1985_p6")], ["2026-10-01T00:00:00+00:00"])
        rows = [row("2026-10-01T00:00:00+00:00", "imo_1985_p6", "lemma-accept", mode="relay-subgoal", lemma=long, lemma_sha="aa"),
                row("2026-11-07T00:00:00+00:00", "imo_1985_p6", "lemma-accept", mode="relay-subgoal", lemma=long, lemma_sha="bb")]
        self.assertEqual(len(stall.progress(rows)[("minif2f/test", "imo_1985_p6")]), 2, "Codex f8: the row keeps 600 chars")

    def test_a_solved_problem_is_never_stalled_and_a_problem_with_no_rows_is_idle_forever(self):
        rows = [row("2026-10-01T00:00:00+00:00", "imo_1985_p6", "accept")]
        s = stall.stalled(rows, OPEN, NOW)
        self.assertEqual([x["target"] for x in s], ["amc12a_2020_p4"])
        self.assertIsNone(s[0]["idle_days"])
        self.assertEqual(s[0]["tries"], 0)


if __name__ == "__main__":
    unittest.main()
