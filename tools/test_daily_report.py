"""tools/daily_report.py: the daily school report reads only the ledger, groups the last 24 hours by grade, names
who passed first, the top performers, the tool-lift series, the Kaggle batches and how long each rung has been
idle. No network."""
import json
import sys
import tempfile
import unittest
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import daily_report

NOW = datetime(2026, 10, 28, 12, 0, tzinfo=timezone.utc)


def row(ts, target, verdict, backend="lane-a", tier="low", mode="ladder-x3", target_set="minif2f/test", rung="amc12"):
    return {"ts": ts, "target": target, "target_set": target_set, "verdict": verdict, "mode": mode,
            "backend": backend, "quality_tier": tier, "rung": rung}


def write(path, rows):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(r) + "\n" for r in rows))


class DailyReport(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.ledger = Path(self.tmp.name) / "ledger"
        write(self.ledger / "minif2f" / "test" / "1.jsonl", [
            row("2026-10-20T10:00:00+00:00", "old", "accept"),                                  # solved long ago
            row("2026-10-28T01:00:00+00:00", "old", "accept", backend="lane-b", tier="tiny"),   # re-solve, not first
            row("2026-10-28T02:00:00+00:00", "new", "accept", backend="lane-b", tier="tiny", mode="prover"),
            row("2026-10-28T03:00:00+00:00", "hard", "reject"),
            row("2026-10-28T03:30:00+00:00", "hard", "reject", backend="lane-b", tier="tiny"),
            row("2026-10-28T04:00:00+00:00", "hard", "error", backend="lane-c", tier="high"),   # not answered
            row("2026-10-27T11:00:00+00:00", "hard", "skipped"),                                # outside and skipped
        ])
        write(self.ledger / "primer" / "1.jsonl", [row("2026-10-28T05:00:00+00:00", "p1", "accept", target_set="primer", rung="primer")])
        write(self.ledger / "speed" / "resolve-1-0.jsonl", [
            {"ts": "2026-10-27T01:00:00+00:00", "run_week": "2026-10-26", "lane": "s3b", "size_b": 3, "target": "t1", "verdict": "accept", "try": 2},
            {"ts": "2026-10-27T01:00:00+00:00", "run_week": "2026-10-26", "lane": "s3b", "size_b": 3, "target": "t2", "verdict": "reject", "try": 1},
            {"ts": "2026-10-27T01:00:00+00:00", "run_week": "2026-10-26", "lane": "s3b", "size_b": 3, "target": "t3", "verdict": "refused", "try": 1},
            {"ts": "2026-10-20T01:00:00+00:00", "run_week": "2026-10-19", "lane": "s3b", "size_b": 3, "target": "t1", "verdict": "reject", "try": 1},
        ])
        write(self.ledger / "prover-batches.jsonl", [{"batch": "goals-1", "answers": 16, "finished_at": "2026-10-28T03:07:20+00:00"}])
        write(self.ledger / "prover-beats" / "failed.jsonl", [{"batch": "tpu32-1", "first_seen_at": "2026-10-27T21:03:11+00:00", "status": "ERROR"}])
        write(self.ledger / "relay-jobs" / "1.json", [])
        (self.ledger / "relay-jobs" / "1.json").write_text(json.dumps({"ts": "2026-10-28T11:00:00+00:00", "backed_off": True, "accepts": 0}))
        write(self.ledger / "openproblems" / "evolve-1.jsonl", [
            {"at": "2026-10-22T22:00:00+00:00", "task": "t", "round": 1, "writer": "lane-w", "reference": {"knnr_py": {"rmse": 0.9688}}, "metrics": {"rmse": 0.99}},
            {"at": "2026-10-22T23:00:00+00:00", "task": "t", "round": 2, "writer": "lane-w", "reference": {"knnr_py": {"rmse": 0.9688}}, "error": "crash"},
        ])
        write(self.ledger / "fc" / "sweep-1.jsonl", [{"at": "2026-10-22T02:00:00+00:00", "name": "e1", "verdict": "open"}])
        (self.ledger / "openproblems" / "qualify-1.json").write_text(json.dumps(
            {"at": "2026-10-22T04:39:28+00:00", "verdict": {"passed": False, "sites": 6, "mean_pearson_delta": -0.0104}}))
        self.report = daily_report.build(self.ledger, NOW)

    def tearDown(self):
        self.tmp.cleanup()

    def test_window_counts_only_answered_tries_in_the_last_24_hours(self):
        t = self.report["totals"]
        self.assertEqual((t["judged"], t["answered"], t["accepted"]), (6, 5, 3))

    def test_first_solves_name_the_target_the_lane_and_the_mode(self):
        self.assertEqual(self.report["first_solves"], [{"grade": "high school", "key": "minif2f/test/new", "lane": "lane-b",
                                                        "tier": "tiny", "mode": "prover", "ts": "2026-10-28T02:00:00+00:00"},
                                                       {"grade": "kindergarten", "key": "primer/p1", "lane": "lane-a",
                                                        "tier": "low", "mode": "ladder-x3", "ts": "2026-10-28T05:00:00+00:00"}])

    def test_grades_rank_lanes_by_accepts_then_answered(self):
        high = next(g for g in self.report["grades"] if g["grade"] == "high school")
        self.assertEqual([(l["lane"], l["answered"], l["accepts"]) for l in high["lanes"]], [("lane-b", 3, 2), ("lane-a", 1, 0)])
        self.assertEqual(high["open"], 1)                      # hard: never accepted
        self.assertEqual(high["solved"], 2)                    # old and new, ever

    def test_speed_series_compares_this_week_to_last_per_lane(self):
        (s,) = self.report["speed"]
        self.assertEqual((s["lane"], s["size_b"], s["week"], s["targets"], s["accepted"], s["refused"]), ("s3b", 3, "2026-10-26", 3, 1, 1))
        self.assertEqual((s["prev_week"], s["prev_accepted"], s["prev_targets"]), ("2026-10-19", 0, 1))

    def test_kaggle_batches_and_failures_in_the_window(self):
        self.assertEqual([b["batch"] for b in self.report["kaggle"]["finished"]], ["goals-1"])
        self.assertEqual([b["batch"] for b in self.report["kaggle"]["failed"]], ["tpu32-1"])

    def test_rungs_report_days_idle_and_the_relay_backoff(self):
        r = {x["rung"]: x for x in self.report["rungs"]}
        self.assertAlmostEqual(r["openproblems.bio"]["idle_days"], 5.5, places=1)
        self.assertEqual(r["openproblems.bio"]["scored"], 1)
        self.assertEqual(r["openproblems.bio"]["qualify"], {"at": "2026-10-22T04:39:28+00:00", "passed": False, "sites": 6, "mean_pearson_delta": -0.0104})
        self.assertAlmostEqual(r["formal-conjectures"]["idle_days"], 6.4, places=1)
        self.assertTrue(self.report["relay"]["backed_off"])

    def test_markdown_carries_the_headline_and_every_grade(self):
        md = daily_report.render(self.report)
        self.assertIn("**2 first-time solves**", md)
        for g in ("kindergarten", "middle school", "high school", "college"):
            self.assertIn(g, md)
        self.assertIn("s3b", md)
        self.assertIn("tpu32-1", md)
        self.assertIn("last qualify missed 2026-10-22", md)        # the bar, never the screen score
        self.assertNotIn("0.99", md)

    def test_an_empty_ledger_is_an_error_not_a_quiet_day(self):
        with self.assertRaises(SystemExit):
            daily_report.build(Path(self.tmp.name) / "nowhere", NOW)


if __name__ == "__main__":
    unittest.main()
