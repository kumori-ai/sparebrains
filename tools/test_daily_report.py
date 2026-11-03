"""tools/daily_report.py: the daily school report reads only the ledger, groups the last 24 hours by grade, names
who passed first, the top performers, the tool-lift series, the Kaggle batches and how long each rung has been
idle. No network."""
import json
import subprocess
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
            dict(row("2026-10-28T04:00:00+00:00", "hard", "error", backend="lane-c", tier="high"),   # not answered
                 reason="KumoriAPIError: kumori /api/v1/llm/chat HTTP 504 : <!DOCTYPE html>"),
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
            {"at": "2026-10-22T23:00:00+00:00", "task": "t", "round": -1, "rescore": {"round": 3}, "reference": {"knnr_py": {"rmse": 0.9688}}, "metrics": {"rmse": 0.98}},
        ])
        (self.ledger / "openproblems" / "drift-ffffffffffff.json").write_text(json.dumps(
            {"at": "2026-10-23T09:00:00+00:00", "pinned": "a" * 40, "main": "f" * 40, "status": "fails", "error": "KeyError: 'seed'"}))
        write(self.ledger / "fc" / "sweep-1.jsonl", [{"at": "2026-10-22T02:00:00+00:00", "name": "e1", "verdict": "open"}])
        (self.ledger / "openproblems" / "qualify-1.json").write_text(json.dumps(
            {"at": "2026-10-22T04:39:28+00:00", "verdict": {"passed": False, "sites": 6, "mean_pearson_delta": -0.0104}}))
        self.report = daily_report.build(self.ledger, NOW)

    def tearDown(self):
        self.tmp.cleanup()

    def test_window_counts_only_answered_tries_in_the_last_24_hours(self):
        t = self.report["totals"]
        self.assertEqual((t["judged"], t["answered"], t["accepted"]), (6, 5, 3))
        self.assertEqual(t["errors"], {"upstream timeout (504)": 1})
        self.assertEqual(self.report["window"]["kind"], "ts", "no git checkout: the last 24 hours by row time")

    def test_recovered_answers_are_counted_apart_with_their_verdicts(self):
        """#597 (2026-11-01): kumori's shared client rescues an answer after Cloudflare's 125 s cut by polling
        /result/<id>, and marks it inference["recovery"] (kumori-96). The report counts those rows apart, by what
        Lean said of them and how many rescues failed, so the 504 line's change can be attributed."""
        rec = lambda ok, orig="http_504_html": {"attempted": True, "succeeded": ok, "original": orig, "cut_at_s": 121.6, "wait_s": 40.2}
        write(self.ledger / "minif2f" / "test" / "r.jsonl", [
            {**row("2026-10-28T06:00:00+00:00", "t9", "accept", backend="slow-a"), "inference": {"recovery": rec(True)}},
            {**row("2026-10-28T06:05:00+00:00", "t9", "reject", backend="slow-a"), "inference": {"recovery": rec(True)}},
            {**row("2026-10-28T06:10:00+00:00", "t9", "error", backend="slow-b"), "reason": "KumoriAPIError: HTTP 524 : no saved answer",
             "inference": {"recovery": rec(False, "524")}},
            {**row("2026-10-20T06:00:00+00:00", "t9", "accept", backend="slow-a"), "inference": {"recovery": rec(True)}},   # outside the window
            {**row("2026-10-28T06:20:00+00:00", "t9", "accept", backend="slow-c"), "upstream_answer_s": 161.3},  # no marker: the clock says it
            {**row("2026-10-28T06:25:00+00:00", "t9", "reject", backend="slow-c"), "upstream_answer_s": 70.0, "upstream_seconds": 140.0},  # two short tries: direct
            {**row("2026-10-28T06:30:00+00:00", "t9", "error", backend="slow-c"), "upstream_answer_s": None, "upstream_seconds": 181.0,
             "reason": "ReadTimeout"},                                                                  # a slow error says nothing about a rescue
            {**row("2026-10-28T06:35:00+00:00", "t9", "accept", backend="slow-c"), "upstream_answer_s": 200.0,
             "inference": {"recovery": {"attempted": False}}},                                          # the marker's no beats the clock
            {**row("2026-10-28T06:40:00+00:00", "t9", "accept", backend="slow-c"), "upstream_answer_s": 90.0},  # an early-drop rescue under 125 s: missed by the clock (residual)
            {**row("2026-10-28T06:45:00+00:00", "t9", "accept", backend="slow-c"), "upstream_answer_s": 90.0,
             "inference": {"recovery": rec(True, "network")}},                                         # the same row with the marker: counted
        ])
        d = daily_report.build(self.ledger, NOW)
        self.assertEqual(d["totals"]["recovered"], {"attempted": 5, "answers": 4, "accepted": 3, "failed": 1, "estimated": 1,
                                                    "by_original": {"http_504_html": 2, "524": 1, "clock>125s": 1, "network": 1}})
        text = daily_report.render(d)
        self.assertIn("Recovered after an edge cut: 4 answers (3 accepted) of 5 rescues tried", text)
        self.assertIn("1 read from the row's clock alone, an estimate", text)
        self.assertNotIn("Recovered after", daily_report.render(self.report), "no line when nothing was rescued")

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

    def test_a_qualify_stopped_at_its_first_fold_renders_without_a_delta(self):
        """Codex 20261102T200554177276Z f2: a screened-out receipt whose one fold errored has mean_pearson_delta None."""
        (self.ledger / "openproblems" / "qualify-2.json").write_text(json.dumps(
            {"at": "2026-10-23T04:39:28+00:00", "verdict": {"passed": False, "sites": 1, "mean_pearson_delta": None}}))
        md = daily_report.render(daily_report.build(self.ledger, NOW))
        self.assertIn("missed 2026-10-23 (Pearson delta unavailable over 1 site", md)

    def test_rungs_report_days_idle_and_the_relay_backoff(self):
        r = {x["rung"]: x for x in self.report["rungs"]}
        self.assertAlmostEqual(r["openproblems.bio"]["idle_days"], 5.5, places=1)
        self.assertEqual(r["openproblems.bio"]["scored"], 1, "a rescore of an earlier candidate is not a round")
        self.assertEqual(r["openproblems.bio"]["drift"], {"at": "2026-10-23T09:00:00+00:00", "main": "ffffffffffff", "status": "fails"})
        self.assertIn("upstream main ffffffffffff FAILS the reproduce gate", daily_report.render(self.report))
        self.assertEqual(r["openproblems.bio"]["qualify"], {"at": "2026-10-22T04:39:28+00:00", "passed": False, "sites": 6, "mean_pearson_delta": -0.0104})
        self.assertAlmostEqual(r["formal-conjectures"]["idle_days"], 6.4, places=1)
        self.assertTrue(self.report["relay"]["backed_off"])

    def test_markdown_carries_the_headline_and_every_grade(self):
        md = daily_report.render(self.report)
        self.assertIn("**2 first-time solves**", md)
        self.assertIn("Lost before the kernel: 1 upstream timeout (504)", md)
        for g in ("kindergarten", "middle school", "high school", "college"):
            self.assertIn(g, md)
        self.assertIn("s3b", md)
        self.assertIn("tpu32-1", md)
        self.assertIn("last qualify missed 2026-10-22", md)        # the bar, never the screen score
        self.assertNotIn("0.99", md)

    def test_an_empty_ledger_is_an_error_not_a_quiet_day(self):
        with self.assertRaises(SystemExit):
            daily_report.build(Path(self.tmp.name) / "nowhere", NOW)


class Arrival(unittest.TestCase):
    """#597 (2026-11-03): the window is the rows that reached the ledger since the last earlier-day report was built,
    not the rows whose ts falls in the last 24 hours. Run 41564483444's rows (ts from 02:16Z) were committed at 07:34Z,
    after the 11-03 report (02:37Z), so a ts window left them out of that report and the next."""

    def git(self, *a):
        return subprocess.run(["git", "-C", str(self.top), *a], check=True, capture_output=True, text=True).stdout.strip()

    def commit(self, msg):
        self.git("add", "-A")
        self.git("commit", "-qm", msg)
        return self.git("rev-parse", "HEAD")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.top = Path(self.tmp.name)
        self.git("init", "-q")
        self.git("config", "user.email", "t@example.invalid")
        self.git("config", "user.name", "t")
        self.ledger, self.daily = self.top / "ledger", self.top / "ledger" / "daily"
        self.rows = self.ledger / "minif2f" / "test" / "run.jsonl"
        self.counted = row("2026-10-27T13:00:00+00:00", "a", "reject")          # in the ts window, but counted yesterday
        write(self.rows, [self.counted])
        self.base = self.commit("rows the 10-27 report saw")
        write(self.daily / "2026-10-27.json", [])
        (self.daily / "2026-10-27.json").write_text(json.dumps({"day": "2026-10-27", "window": {"built_from": self.base}}))
        self.commit("the 10-27 report")
        self.late = row("2026-10-26T20:00:00+00:00", "b", "accept")             # stamped before that report, landed after
        self.fresh = row("2026-10-28T05:00:00+00:00", "c", "reject")
        write(self.rows, [self.counted, self.late, self.fresh])
        self.head = self.commit("a run that ended after the report")

    def tearDown(self):
        self.tmp.cleanup()

    def test_counts_what_arrived_since_the_last_report_once(self):
        d = daily_report.build(self.ledger, NOW)
        self.assertEqual(d["window"], {"kind": "arrived", "from": self.base, "from_report": "2026-10-27", "built_from": self.head})
        self.assertEqual((d["totals"]["judged"], d["totals"]["accepted"]), (2, 1))
        self.assertEqual([f["key"] for f in d["first_solves"]], ["minif2f/test/b"], "a late first solve is still reported")
        self.assertIn("rows that reached the ledger since the 2026-10-27 report", daily_report.render(d))

    def test_a_second_report_the_same_day_starts_from_the_earlier_day(self):
        (self.daily / "2026-10-28.json").write_text(json.dumps({"day": "2026-10-28", "window": {"built_from": self.head}}))
        self.commit("this morning's report")
        d = daily_report.build(self.ledger, NOW)
        self.assertEqual((d["window"]["from"], d["totals"]["judged"]), (self.base, 2))

    def test_uncommitted_rows_wait_for_their_commit(self):
        write(self.rows, [self.counted, self.late, self.fresh, row("2026-10-28T06:00:00+00:00", "d", "reject")])
        self.assertEqual(daily_report.build(self.ledger, NOW)["totals"]["judged"], 2)

    def test_the_transition_day_starts_from_the_parent_of_the_commit_that_wrote_the_last_page(self):
        (self.daily / "2026-10-27.json").write_text(json.dumps({"day": "2026-10-27"}))     # a page from before built_from
        wrote = self.commit("the 10-27 report, rewritten without built_from")
        write(self.rows, [self.counted, self.late, self.fresh, row("2026-10-27T01:00:00+00:00", "d", "reject")])
        self.commit("a run that ended after it")
        d = daily_report.build(self.ledger, NOW)
        self.assertEqual(d["window"]["kind"], "arrived")
        self.assertEqual(d["window"]["from"], self.git("rev-parse", f"{wrote}^"))
        self.assertIn("predates built_from", d["window"]["base"])
        self.assertEqual(d["totals"]["judged"], 1, "what landed after that page, not before it")

    def test_an_unreadable_checkpoint_stops_the_report_instead_of_skipping_rows(self):
        """Codex f1: a ts fallback here would write built_from = HEAD and so skip, for good, every late row outside
        its own ts window."""
        (self.daily / "2026-10-27.json").write_text(json.dumps({"window": {"built_from": "f" * 40}}))
        with self.assertRaises(SystemExit):
            daily_report.build(self.ledger, NOW)
        with tempfile.TemporaryDirectory() as td:
            clone = Path(td) / "shallow"
            subprocess.run(["git", "clone", "-q", "--depth=1", self.top.as_uri(), str(clone)], check=True)
            (clone / "ledger" / "daily" / "2026-10-27.json").write_text(json.dumps({"window": {"built_from": self.base}}))
            with self.assertRaises(SystemExit):
                daily_report.build(clone / "ledger", NOW)

    def test_a_late_row_is_counted_exactly_once_across_days(self):
        first = daily_report.build(self.ledger, NOW)
        (self.daily / "2026-10-28.json").write_text(json.dumps(first))
        self.commit("the 10-28 report")
        later = row("2026-10-28T11:00:00+00:00", "e", "accept")            # stamped before the 10-28 page, landed after
        write(self.rows, [self.counted, self.late, self.fresh, later])
        self.commit("another late run")
        second = daily_report.build(self.ledger, datetime(2026, 10, 29, 12, 0, tzinfo=timezone.utc))
        self.assertEqual(second["window"]["from"], first["window"]["built_from"])
        self.assertEqual((first["totals"]["judged"], second["totals"]["judged"]), (2, 1))
        self.assertEqual([f["key"] for f in second["first_solves"]], ["minif2f/test/e"])

    def test_identical_rows_count_by_occurrence(self):
        """Codex f3: a row added that is byte-identical to an older one counts once, not twice."""
        write(self.rows, [self.counted, self.late, self.fresh, self.counted])
        self.commit("an identical row again")
        self.assertEqual(daily_report.build(self.ledger, NOW)["totals"]["judged"], 3)

    def test_an_old_accept_added_again_is_one_arrival_and_no_first_solve(self):
        """Codex f3, round 2: yesterday's accept duplicated today counts once and is not a first solve again."""
        first = daily_report.build(self.ledger, NOW)
        (self.daily / "2026-10-28.json").write_text(json.dumps(first))
        self.commit("the 10-28 report")
        write(self.rows, [self.counted, self.late, self.fresh, self.late])
        self.commit("the late accept, again")
        second = daily_report.build(self.ledger, datetime(2026, 10, 29, 12, 0, tzinfo=timezone.utc))
        self.assertEqual([f["key"] for f in first["first_solves"]], ["minif2f/test/b"])
        self.assertEqual((second["totals"]["judged"], second["totals"]["accepted"], second["first_solves"]), (1, 1, []))

    def test_a_failed_diff_stops_the_report_and_a_retry_still_counts_the_late_row(self):
        """Codex f1, round 2: a diff that fails must not fall back and move the checkpoint past the late row."""
        real = daily_report.git
        daily_report.git = lambda top, *a: None if a[:1] == ("diff",) else real(top, *a)
        try:
            with self.assertRaises(SystemExit):
                daily_report.build(self.ledger, NOW)
        finally:
            daily_report.git = real
        self.assertEqual([f["key"] for f in daily_report.build(self.ledger, NOW)["first_solves"]], ["minif2f/test/b"])

    def test_main_warns_when_there_is_no_earlier_report(self):
        (self.daily / "2026-10-27.json").unlink()
        import io, contextlib
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            daily_report.main(["--ledger", str(self.ledger), "--out", str(self.daily), "--now", NOW.isoformat()])
        self.assertIn("::warning::daily report counted by row time, not arrival: no earlier report", buf.getvalue())
        self.assertEqual(json.loads((self.daily / "2026-10-28.json").read_text())["window"]["built_from"], self.git("rev-parse", "HEAD"))

if __name__ == "__main__":
    unittest.main()
