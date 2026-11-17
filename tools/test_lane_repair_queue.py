"""Durable quota deferral: original budget, crash reservations and due-time admission."""
import tempfile
import unittest
import json
import os
from pathlib import Path
from unittest import mock

import lane_repair_queue as q


class Requests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.path = q.enqueue(self.root, "123", "unknown_name", "first,last", 12, now=1000)

    def state(self):
        return q.state(q.read(self.path))

    def test_enqueue_is_idempotent_but_cannot_reset_or_change_budget(self):
        q.enqueue(self.root, "123", "unknown_name", "first,last", 12, now=2000)
        self.assertEqual(len(q.read(self.path)), 1)
        with self.assertRaises(ValueError):
            q.enqueue(self.root, "123", "unknown_name", "first,last", 13, now=2000)
        self.assertEqual(self.state()["remaining"], 12)

    def test_zero_admission_defers_without_starting_or_spending(self):
        calls = []
        def admission(lane, need):
            calls.append((lane, need))
            return {"eligible_now": False, "next_check_at": 3000, "reason": "held_for_others"}
        selected = q.select(self.root, admission, now=1100)
        self.assertIsNone(selected)
        self.assertEqual(calls, [("first", 12), ("last", 12)])
        s = self.state()
        self.assertEqual((s["status"], s["remaining"], s["due"]), ("deferred", 12, 3000))
        self.assertIsNone(q.select(self.root, admission, now=2000))
        self.assertEqual(len(calls), 2)

    def test_late_refusal_preserves_partial_progress_and_remaining_budget(self):
        q.start(self.path, "500-1", ["first"], now=1100)
        self.assertEqual(self.state()["remaining"], 0)
        q.finish(self.path, "500-1", [
            {"writer": "first", "repair_asks": 1, "repair_refused": "quota"},
            {"writer": None, "refused": "every writer refused"},
        ], now=1200)
        s = self.state()
        self.assertEqual((s["status"], s["remaining"]), ("deferred", 10))
        q.start(self.path, "501-1", ["last"], now=2200)
        q.finish(self.path, "501-1", [{"writer": "last", "repair_asks": 9}], now=2300)
        self.assertEqual((self.state()["status"], self.state()["remaining"]), ("complete", 0))

    def test_crash_reservation_is_not_automatically_retried(self):
        q.start(self.path, "500-1", ["first"], now=1100)
        self.assertEqual((self.state()["status"], self.state()["remaining"]), ("started", 0))
        def forbidden(*args):
            self.fail("an unresolved reservation must never make another admission request")
        self.assertIsNone(q.select(self.root, forbidden, now=100000))
        with self.assertRaises(ValueError):
            q.start(self.path, "501-1", ["first"], now=2000)

    def test_fallback_is_explicit_and_admission_errors_fail_closed(self):
        def admission(lane, need):
            if lane == "first":
                raise RuntimeError("admission unavailable")
            return {"eligible_now": True}
        selected = q.select(self.root, admission, now=1100)
        self.assertEqual(selected["lanes"], ["last"])
        with self.assertRaises(ValueError):
            q.start(self.path, "500-1", ["unrequested"], now=1100)

    def test_failure_does_not_release_an_unknown_budget(self):
        q.start(self.path, "500-1", ["first"], now=1100)
        q.finish(self.path, "500-1", [{"writer": "first", "repair_asks": 0}], now=1200, success=False)
        self.assertEqual((self.state()["status"], self.state()["remaining"]), ("interrupted", 0))

    def test_budget_cannot_be_overdrawn_or_refunded_twice(self):
        q.start(self.path, "500-1", ["first"], now=1100)
        with self.assertRaises(ValueError):
            q.finish(self.path, "500-1", [{"writer": "first", "repair_asks": 12}], now=1200)
        q.finish(self.path, "500-1", [{"writer": "first", "repair_asks": 0, "repair_refused": "quota"}], now=1200)
        with self.assertRaises(ValueError):
            q.finish(self.path, "500-1", [], now=1200)
        self.assertEqual(self.state()["remaining"], 11)

    def test_ordinary_completion_and_empty_results_do_not_retry(self):
        q.start(self.path, "500-1", ["first"], now=1100)
        q.finish(self.path, "500-1", [], now=1200)
        self.assertEqual(self.state()["status"], "interrupted")

    def test_expired_request_is_visible_and_does_not_call_admission(self):
        def forbidden(*args):
            self.fail("expired request reached admission")
        self.assertIsNone(q.select(self.root, forbidden, now=1000 + q.MAX_AGE + 1))
        self.assertEqual(self.state()["status"], "blocked")

    def test_setup_interruption_is_not_repeated_automatically(self):
        q.select(self.root, lambda *a: {"eligible_now": True}, now=1100)
        self.assertEqual(self.state()["status"], "admitted")
        def forbidden(*args):
            self.fail("setup interruption must stop for review")
        self.assertIsNone(q.select(self.root, forbidden, now=2000))
        self.assertEqual(self.state()["remaining"], 12)

    def test_stranded_admission_becomes_visibly_blocked_only_after_the_job_could_not_still_run(self):
        q.select(self.root, lambda *a: {"eligible_now": True}, now=1100)
        def forbidden(*args):
            self.fail("a stranded request must not reach admission")
        q.select(self.root, forbidden, now=1100 + q.STALE - 1)
        self.assertEqual(self.state()["status"], "admitted")
        q.select(self.root, forbidden, now=1100 + q.STALE)
        self.assertEqual((self.state()["status"], self.state()["remaining"]), ("blocked", 12))

    def test_stranded_reservation_ends_interrupted_with_nothing_refunded(self):
        q.start(self.path, "500-1", ["first"], now=1100)
        q.select(self.root, lambda *a: self.fail("no admission"), now=1100 + q.STALE)
        self.assertEqual((self.state()["status"], self.state()["remaining"]), ("interrupted", 0))

    def test_reservation_whose_model_step_never_started_is_released_not_charged(self):
        q.start(self.path, "500-1", ["first"], now=1100)
        q.release(self.path, "500-1", now=1200)
        self.assertEqual((self.state()["status"], self.state()["remaining"]), ("blocked", 12))
        self.assertIsNone(q.select(self.root, lambda *a: self.fail("blocked stays blocked"), now=100000))

    def test_one_unreadable_request_does_not_stop_the_others(self):
        (self.root / "99.jsonl").write_text("not json\n")
        (self.root / "98.jsonl").write_text(json.dumps({"event": "finished"}) + "\n")
        selected = q.select(self.root, lambda *a: {"eligible_now": True}, now=1100)
        self.assertEqual(selected["request"], "123")

    def test_only_three_admission_fields_reach_the_public_ledger(self):
        reply = {"eligible_now": False, "reason": "held_for_others " + "x" * 500, "next_check_at": 3000,
                 "tenants": {"production": 1, "evals": 76}, "caller": "private-detail"}
        q.select(self.root, lambda *a: dict(reply), now=1100)
        text = self.path.read_text()
        self.assertNotIn("tenants", text)
        self.assertNotIn("private-detail", text)
        kept = q.read(self.path)[-1]["admission"]["first"]
        self.assertEqual(set(kept), {"eligible_now", "reason", "next_check_at"})
        self.assertLessEqual(len(kept["reason"]), 200)
        self.assertEqual(self.state()["due"], 3000)

    def test_unknown_meter_state_never_admits(self):
        for response in ({}, {"eligible_now": None}, {"eligible_now": "true"}):
            with self.subTest(response=response):
                result = q.select(self.root, lambda *a: response, now=100000)
                self.assertIsNone(result)
                self.assertEqual(self.state()["remaining"], 12)
                self.assertEqual(self.state()["status"], "deferred")
                # Make the next independent response due without modifying its budget.
                q.append(self.path, {"event": "deferred", "at": 100000, "due": 100000})

    def test_retry_bounds_end_in_visible_blocked_state_without_spending(self):
        for index in range(q.MAX_CHECKS):
            q.append(self.path, {"event": "deferred", "at": 1000 + index, "due": 1000})
        def forbidden(*args):
            self.fail("check limit must stop before admission")
        self.assertIsNone(q.select(self.root, forbidden, now=2000))
        self.assertEqual((self.state()["status"], self.state()["remaining"]), ("blocked", 12))

    def test_zero_use_late_refusals_cannot_retry_without_bound(self):
        for index in range(q.MAX_ATTEMPTS):
            attempt = f"{500 + index}-1"
            q.start(self.path, attempt, ["first"], now=1000 + index * 1000)
            q.finish(self.path, attempt, [{"writer": None, "refused": "quota"}], now=1001 + index * 1000)
        def forbidden(*args):
            self.fail("attempt limit must stop before admission")
        self.assertIsNone(q.select(self.root, forbidden, now=20000))
        self.assertEqual((self.state()["status"], self.state()["remaining"]), ("blocked", 12))

    def test_bad_input_cannot_escape_ledger_or_inject_workflow_commands(self):
        for request, lanes, rounds in [("../escape", "first", 12), ("124", "first\nbad", 12),
                                        ("124", "first", 0), ("124", "first", 13)]:
            with self.assertRaises(ValueError):
                q.enqueue(self.root, request, "unknown_name", lanes, rounds, now=1000)


class Workflow(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.queue = self.root / "ledger" / "lane-repair-requests"
        self.selected = self.root / "selection.json"
        self.outputs = self.root / "outputs"
        for patch in (mock.patch.object(q, "ROOT", self.root), mock.patch.object(q, "QUEUE", self.queue),
                      mock.patch.dict(os.environ, {"GITHUB_RUN_ID": "123", "GITHUB_RUN_ATTEMPT": "1",
                                                   "GITHUB_OUTPUT": str(self.outputs),
                                                   "INPUT_CLASS": "unknown_name", "INPUT_LANES": "first,last",
                                                   "INPUT_ROUNDS": "12"}),
                      mock.patch.object(q.time, "time", return_value=1000)):
            patch.start()
            self.addCleanup(patch.stop)
        self.publish = mock.patch.object(q, "publish_events")
        self.publisher = self.publish.start()
        self.addCleanup(self.publish.stop)
        q.main(["enqueue"])

    def invoke(self, command, *args, admission=None):
        return q.main([command, "--selection", str(self.selected), *args], admission=admission)

    def test_zero_capacity_emits_no_setup_signal_and_keeps_request(self):
        self.invoke("select", admission=lambda *a: {"eligible_now": False, "next_check_at": 2000})
        self.assertEqual(self.outputs.read_text(), "ready=false\n")
        self.assertFalse(self.selected.exists())
        s = q.state(q.read(self.queue / "123.jsonl"))
        self.assertEqual((s["status"], s["remaining"]), ("deferred", 12))

    def test_admission_publication_failure_cannot_enable_expensive_setup(self):
        self.publisher.side_effect = RuntimeError("publication failed")
        with self.assertRaises(RuntimeError):
            self.invoke("select", admission=lambda *a: {"eligible_now": True})
        self.assertFalse(self.outputs.exists())
        self.assertFalse(self.selected.exists())

    def test_model_phase_requires_reservation_and_uses_only_its_remaining_budget(self):
        self.invoke("select", admission=lambda *a: {"eligible_now": True})
        with mock.patch.object(q.subprocess, "run") as run:
            with self.assertRaises(ValueError):
                self.invoke("run")
            run.assert_not_called()
            self.invoke("start")
            run.return_value.returncode = 0
            self.invoke("run")
            args = run.call_args.args[0]
            self.assertEqual(args[args.index("--rounds") + 1], "12")
            self.assertEqual(args[args.index("--lanes") + 1], "first,last")
            out = Path(args[args.index("--out") + 1])
            out.parent.mkdir(parents=True)
            out.write_text(json.dumps({"writer": "first", "repair_asks": 2, "repair_refused": "quota"}) + "\n")
        self.invoke("finish", "--success")
        self.assertEqual(q.state(q.read(self.queue / "123.jsonl"))["remaining"], 9)
        with mock.patch.object(q.time, "time", return_value=2000):
            self.invoke("select", admission=lambda *a: {"eligible_now": True})
            self.invoke("start", "--attempt", "124-1")
            with mock.patch.object(q.subprocess, "run") as run:
                run.return_value.returncode = 0
                self.invoke("run", "--attempt", "124-1")
                args = run.call_args.args[0]
                self.assertEqual(args[args.index("--rounds") + 1], "9")

    def test_reservation_that_failed_to_publish_is_not_recorded_as_spent(self):
        self.invoke("select", admission=lambda *a: {"eligible_now": True})
        self.publisher.side_effect = RuntimeError("publication failed")
        with self.assertRaises(RuntimeError):
            self.invoke("start")
        self.invoke("abort")
        s = q.state(q.read(self.queue / "123.jsonl"))
        self.assertEqual((s["status"], s["remaining"]), ("blocked", 12))

    def test_setup_failure_is_persisted_as_blocked_with_unspent_budget(self):
        self.invoke("select", admission=lambda *a: {"eligible_now": True})
        self.invoke("abort")
        s = q.state(q.read(self.queue / "123.jsonl"))
        self.assertEqual((s["status"], s["remaining"]), ("blocked", 12))


if __name__ == "__main__":
    unittest.main()
