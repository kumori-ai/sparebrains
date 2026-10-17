import json, sys, tempfile, unittest
from pathlib import Path

sys.path[:0] = [str(Path(__file__).resolve().parent)]
import prover

NAME = "mathd_algebra_478"
SKETCH = f"```lean4\ntheorem {NAME} (x : ℝ) : x = x := by\n  have h : x = x := by\n    sorry\n  sorry\n```"
FULL = f"```lean4\ntheorem {NAME} (x : ℝ) : x = x := by\n  rfl\n```"


def answer(sample, text=FULL, target=NAME, batch="b1"):
    return {"batch": batch, "target_set": "minif2f/test", "target": target, "sample": sample, "text": text,
            "tokens": 10, "finish": "stop", "seconds": 1.0, "config": {"model": prover.MODEL}}


class Rec:
    def __init__(self):
        self.rows, self.proofs = [], []

    def __call__(self, row, response, proof, candidate, lean_out):
        self.rows.append(row)

    def verified(self, tset, name, candidate):
        self.proofs.append(name)


def judge_by(verdicts):
    calls = []
    def judge_text(text):
        calls.append(text)
        v = verdicts.pop(0) if verdicts else "reject"
        return {"verdict": v, "reason": "" if v == "accept" else "unsolved goals", "output": "error: unsolved goals"}
    judge_text.calls = calls
    return judge_text


class ProverTests(unittest.TestCase):
    def run_judge(self, answers, verdicts, rows=(), fix=lambda p, o: (p, []), repair=lambda c, p, o: {}):
        rec, jt = Rec(), judge_by(list(verdicts))
        stats = prover.judge_answers(answers, list(rows), judge_text=jt, fix=fix, repair=repair, record=rec,
                                     run_id="prover-b1")
        return rec, jt, stats

    def test_the_last_complete_block_is_judged_not_the_sketch(self):
        self.assertIn("rfl", prover.final_proof("plan\n" + SKETCH + "\nnow the proof\n" + FULL, NAME))
        self.assertIn("sorry", prover.final_proof(SKETCH, NAME))
        self.assertIsNone(prover.final_proof("no lean here", NAME))

    def test_a_problem_stops_at_its_first_accept(self):
        rec, jt, stats = self.run_judge([answer(0, FULL.replace("rfl", "simp")), answer(1), answer(2)], ["reject", "accept"])
        self.assertEqual([r["verdict"] for r in rec.rows], ["reject", "accept"])
        self.assertEqual(rec.proofs, [NAME])
        self.assertEqual(stats["solved"], 1)

    def test_a_repeated_proof_is_not_judged_twice(self):
        rec, jt, _ = self.run_judge([answer(0), answer(1)], ["reject", "accept"])
        self.assertEqual(len(jt.calls), 1)
        self.assertEqual([r["verdict"] for r in rec.rows], ["reject", "reject"])

    def test_answers_already_judged_are_skipped(self):
        done = [{"backend": prover.BACKEND, "try_mode": "prover", "batch": "b1", "target_set": "minif2f/test",
                 "target": NAME, "sample_no": 0, "verdict": "reject"}]
        rec, _, _ = self.run_judge([answer(0), answer(1)], ["accept"], rows=done)
        self.assertEqual([r["sample_no"] for r in rec.rows], [1])

    def test_the_loop_turns_a_miss_and_is_recorded_beside_the_raw_row(self):
        rec, _, stats = self.run_judge([answer(0)], ["reject"], repair=lambda c, p, o: {"accepted": c, "closed_by_lean": 2})
        self.assertEqual([(r["try_mode"], r["verdict"]) for r in rec.rows], [("prover", "reject"), ("fixer+loop", "accept")])
        self.assertEqual(stats["solved_by_loop"], 1)

    def test_answers_after_a_solve_are_not_owed(self):
        rows = [{"backend": prover.BACKEND, "try_mode": "prover", "batch": "b1", "target_set": "minif2f/test",
                 "target": NAME, "sample_no": 0, "verdict": "accept"}]
        self.assertEqual(prover.to_judge([answer(0), answer(1), answer(2)], rows), {})
        closed = prover.to_judge([answer(1)], [], still_open={("minif2f/test", "other")})
        self.assertEqual(closed, {}, "a problem solved elsewhere owes nothing")

    def test_no_proof_in_the_answer_is_a_reject_with_no_lean_run(self):
        rec, jt, _ = self.run_judge([answer(0, "I could not prove it.")], [])
        self.assertEqual(rec.rows[0]["verdict"], "reject")
        self.assertEqual(jt.calls, [])

    def test_todo_takes_only_the_bars_rungs_and_what_is_owed(self):
        open_list = [{"target_set": "minif2f/test", "target": "a", "rung": "amc12", "order": 2},
                     {"target_set": "minif2f/test", "target": "b", "rung": "imo", "order": 1},
                     {"target_set": "minif2f/test", "target": "c", "rung": "math-L5", "order": 3}]
        rows = [{"backend": prover.BACKEND, "try_mode": "prover", "batch": "b1", "target_set": "minif2f/test",
                 "target": "a", "sample_no": i} for i in range(30)]
        self.assertEqual([(t["target"], n) for t, n in prover.todo(open_list, rows)], [("a", 2), ("c", 32)])

    def test_build_fills_the_kernel(self):
        with tempfile.TemporaryDirectory() as d:
            t = {"target_set": "minif2f/test", "target": NAME, "rung": "math-L1", "order": 1}
            prover.build(d, [(t, 32)], "b9")
            src = (Path(d) / "prover_kernel.py").read_text()
            meta = json.loads((Path(d) / "kernel-metadata.json").read_text())
            self.assertIn('BATCH = "b9"', src)
            self.assertIn(f"theorem {NAME}", src)
            self.assertEqual(meta["machine_shape"], "NvidiaTeslaT4")
            self.assertEqual(meta["is_private"], "false", "the record is public, the Kaggle half included")
            compile(src, "prover_kernel.py", "exec")


class BatchTimingTests(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.old = prover.BATCHES
        prover.BATCHES = Path(self.d.name) / "prover-batches.jsonl"

    def tearDown(self):
        prover.BATCHES = self.old
        self.d.cleanup()

    def test_exact_times_from_the_scripts_timing_file(self):
        from datetime import datetime, timezone
        k = Path(self.d.name) / "k1"
        k.mkdir()
        (k / "timing.json").write_text(json.dumps({"started_at": "2026-10-17T20:30:41+00:00", "load_s": 330,
                                                   "finished_at": "2026-10-18T02:30:41+00:00"}))
        rec = prover.batch_record(k, "20261017T1830", datetime(2026, 10, 18, 4, tzinfo=timezone.utc),
                                  [{"tokens": 3600}] * 10)
        self.assertEqual((rec["queued_min"], rec["ran_min"], rec["tok_per_s"]), (120.7, 360.0, 1.7))
        self.assertIsNone(prover.batch_record(k, "20261017T1830", datetime.now(timezone.utc)), "written once per batch")

    def test_without_a_timing_file_the_queue_is_an_upper_bound(self):
        from datetime import datetime, timezone
        k = Path(self.d.name) / "k2"
        k.mkdir()
        (k / "sparebrains-prover.log").write_text('[{"time":0.7,"data":"x"}\n,{"time":3600.0,"data":"y"}]')
        rec = prover.batch_record(k, "20261017T1830", datetime(2026, 10, 17, 22, 30, tzinfo=timezone.utc))
        self.assertEqual((rec["ran_min"], rec["queued_min_at_most"]), (60.0, 180.0))
        self.assertIn("upper bound", rec["source"])


if __name__ == "__main__":
    unittest.main()
