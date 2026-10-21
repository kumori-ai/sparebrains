import json, sys, tempfile, unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path[:0] = [str(Path(__file__).resolve().parent)]
import prover

NAME = "mathd_algebra_478"
FRI_NIGHT = datetime(2026, 10, 23, 23, 0, tzinfo=timezone.utc)   # an hour before the weekly reset
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
        self.assertEqual([(t["target"], n) for t, n in prover.todo(open_list, rows, bar=False)], [("b", 32)])

    def test_the_32b_takes_reachable_open_problems_and_the_bar_only_after_the_plan_arm(self):
        open_list = [{"target_set": "minif2f/test", "target": t, "rung": r, "order": i}
                     for i, (t, r) in enumerate([("a", "amc12"), ("b", "imo"), ("c", "custom"), ("d", "aime")])]
        reach = {("minif2f/test", "a"), ("minif2f/test", "b"), ("minif2f/test", "d")}
        rows = [{"backend": prover.PROVER_32B["backend"], "try_mode": "prover-32b", "batch": "t1",
                 "target_set": "minif2f/test", "target": "b", "sample_no": i} for i in range(prover.SAMPLES)]
        rows.append({"backend": prover.BACKEND, "try_mode": "prover", "batch": "g1", "target_set": "minif2f/test",
                     "target": "a", "sample_no": 0})                                     # the 8B's samples do not count
        self.assertEqual([(t["target"], n) for t, n in prover.reachable_work(open_list, rows, reach, bar=False)], [])
        self.assertEqual([(t["target"], n) for t, n in prover.reachable_work(open_list, rows, reach, bar=True)],
                         [("a", 32), ("d", 32)])

    def test_a_32b_answer_is_judged_and_credited_as_the_32b(self):
        a = {**answer(0), "config": {"model": prover.PROVER_32B["model"]}}
        self.assertIs(prover.lane_for([a]), prover.PROVER_32B)
        self.assertIs(prover.lane_for([answer(0)]), prover.PROVER)
        self.assertNotEqual(prover.PROVER_32B["mode"], prover.PROVER["mode"])

    def test_a_32b_tpu_kernel_names_the_32b(self):
        with tempfile.TemporaryDirectory() as d:
            t = {"target_set": "minif2f/test", "target": NAME, "rung": "imo", "order": 1}
            prover.build(d, [(t, 32)], "tpu32-20261023T0000", tpu=True, budget_h=8.5, model=prover.PROVER_32B["model"])
            self.assertIn('MODEL = "Goedel-LM/Goedel-Prover-V2-32B"', (Path(d) / "prover_kernel.py").read_text())

    def test_a_tpu_kernel_gets_its_budget_less_the_load_and_one_chunk(self):
        with tempfile.TemporaryDirectory() as d:
            t = {"target_set": "minif2f/test", "target": NAME, "rung": "imo", "order": 1}
            prover.build(d, [(t, 32)], "tpu-20261020T2300", tpu=True, budget_h=8.5)
            src = (Path(d) / "prover_kernel.py").read_text()
            self.assertIn(f"BUDGET_S = {int((8.5 - prover.TPU_RESERVE_H) * 3600)}", src)
            self.assertEqual(json.loads((Path(d) / "kernel-metadata.json").read_text())["id"], prover.KERNEL_ID_TPU)

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


TARGET = f"import Mathlib\n\nopen Real\n\n/-- What is x? -/\ntheorem {NAME} (x : ℝ) : x = x := by\n  sorry\n"


class PlanArmTests(unittest.TestCase):
    """Task #433: the prover alone and with a plain-math plan, same problems, same batch, each arm judged alone."""

    def test_the_plan_is_a_comment_before_the_theorem_and_nothing_else_moves(self):
        s = prover.with_plan(TARGET, "Both sides are x.")
        self.assertIn("/- A plan for this proof, in plain mathematics (drafted with Claude", s)
        self.assertLess(s.index("Both sides are x."), s.index("/-- What is x? -/"))
        self.assertEqual(s.replace(s[s.index("/- A plan"):s.index("/-- What")], ""), TARGET)

    def test_both_arms_sit_side_by_side_so_a_budget_stop_cuts_them_equally(self):
        doc = {"id": "p1", "plans": [{"target_set": "minif2f/test", "target": "a", "plan": "x"},
                                     {"target_set": "minif2f/test", "target": "b", "plan": "y"}]}
        work = prover.plan_work(doc, {("minif2f/test", "b")}, read=lambda s, t: TARGET)
        self.assertEqual([(w["target"], w["arm"], w["n"]) for w in work], [("b", "alone", 4), ("b", "plan", 4)])
        self.assertEqual(work[0]["statement"], TARGET)
        self.assertIn("y", work[1]["statement"])

    def test_each_arm_is_judged_on_its_own_and_stops_at_its_own_first_accept(self):
        ans = [dict(answer(k, batch="plan-p1-20261024T0000"), arm=arm) for arm in ("plan", "alone") for k in range(3)]
        rec, rows = Rec(), []
        jt = judge_by(["reject", "accept", "reject", "reject", "accept"])
        stats = prover.judge_plan(ans, judge_text=jt, record=rec, run_id="prover-plan", read=lambda s, t: TARGET,
                                  out=rows.append, plans_id="p1")
        self.assertEqual([(r["arm"], r["sample_no"], r["verdict"]) for r in rows],
                         [("alone", 0, "reject"), ("alone", 1, "accept"),
                          ("plan", 0, "reject"), ("plan", 1, "reject"), ("plan", 2, "accept")])
        self.assertEqual((stats["alone"], stats["plan"]), ({"solved": 1, "samples": 2}, {"solved": 1, "samples": 3}))
        self.assertEqual([r["try_mode"] for r in rec.rows], ["prover", "prover+plan"])   # first accepts, as tries
        self.assertEqual(rec.proofs, [NAME], "one verified file per problem")
        self.assertTrue(all(r["plans_id"] == "p1" for r in rows))

    def test_a_budget_cut_plan_batch_leaves_the_rest_owed_and_the_verdict_pools_both_runs(self):
        doc = {"id": "p1", "plans": [{"target_set": "minif2f/test", "target": t, "plan": "x"} for t in "abc"]}
        row = lambda t, arm, v="reject", pid="p1": {"target_set": "minif2f/test", "target": t, "arm": arm,
                                                    "plans_id": pid, "verdict": v}
        with tempfile.TemporaryDirectory() as d:
            plans, arm_dir = Path(d) / "plans.json", Path(d) / "plan-arm"
            plans.write_text(json.dumps(doc))
            arm_dir.mkdir()
            (arm_dir / "rows-plan-p1-1.jsonl").write_text("".join(json.dumps(r) + "\n" for r in
                [row("a", "alone"), row("a", "plan", "accept"), row("b", "alone"), row("c", "alone", pid="p0")]))
            owed = prover.plan_owed(d, plans)
            self.assertEqual([p["target"] for p in owed["plans"]], ["b", "c"], "b lacks its plan arm, c ran under another id")
            (arm_dir / "rows-plan-p1-2.jsonl").write_text("".join(json.dumps(r) + "\n" for r in
                [row("b", "plan", "accept"), row("c", "alone", "accept"), row("c", "plan")]))
            self.assertIsNone(prover.plan_owed(d, plans))
            v = prover.plan_verdict(prover.plan_rows("p1", d))
            self.assertEqual((v["problems"], v["only_plan"], v["only_alone"]), (3, ["a", "b"], ["c"]))

    def test_batch_ids_with_a_prefix_parse(self):
        from datetime import datetime, timezone
        old = prover.BATCHES
        with tempfile.TemporaryDirectory() as d:
            prover.BATCHES = Path(d) / "b.jsonl"
            try:
                for b in ("plan-p1-20261024T0000", "goals-20261024T0000"):
                    rec = prover.batch_record(d, b, datetime(2026, 10, 24, 6, tzinfo=timezone.utc))
                    self.assertEqual(rec["pushed_at"], "2026-10-24T00:00:00+00:00")
            finally:
                prover.BATCHES = old


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


class GpuHoursTests(unittest.TestCase):
    """The week's GPU hours used exactly (2026-10-19): the batch is sized to what Kaggle says is left."""

    def test_a_batch_gets_the_hours_left_less_the_margin_at_most_one_session(self):
        late = FRI_NIGHT                                                    # pacing allows the whole week by now
        self.assertEqual(prover.batch_hours(30, 20.57, now=late), round(30 - 20.57 - prover.MARGIN_H, 2))
        self.assertEqual(prover.batch_hours(39, 0, now=late), prover.SESSION_H)       # a floating week above 30 h
        self.assertEqual(prover.batch_hours(30, 28.5, now=late), 0.0)                  # under the floor: wait for the reset
        self.assertEqual(prover.batch_hours(30, 20, reserved_h=9.5, now=late), 0.0)    # a live session holds the rest

    def test_the_week_is_spent_on_an_even_line_at_most_a_day_ahead(self):
        sat = datetime(2026, 10, 24, 0, 30, tzinfo=timezone.utc)            # just after the reset
        day = 30 / 7
        self.assertEqual(prover.batch_hours(30, 0, now=sat), round(30 * (0.5 + 24) / 168, 2))     # one day's share
        self.assertEqual(prover.batch_hours(30, day, now=sat + timedelta(hours=2)), 0.0)          # today's is spent
        self.assertEqual(prover.batch_hours(30, day, now=sat + timedelta(hours=24)),
                         round(30 * (24.5 + 24) / 168 - day, 2))                                  # tomorrow's opens
        self.assertEqual(prover.batch_hours(30, 0, now=sat + timedelta(days=3)), prover.SESSION_H)  # behind: catch up

    def test_the_tpu_gets_its_own_session_and_floor(self):
        late = FRI_NIGHT
        self.assertEqual(prover.batch_hours(20, 0, tpu=True, now=late), prover.TPU_SESSION_H)
        self.assertEqual(prover.batch_hours(20, 15, tpu=True, now=late), round(20 - 15 - prover.MARGIN_H, 2))
        self.assertEqual(prover.batch_hours(20, 18, tpu=True, now=late), 0.0)          # under the TPU floor: wait for the reset
        sat = datetime(2026, 10, 24, 0, 30, tzinfo=timezone.utc)
        self.assertEqual(prover.batch_hours(20, 0, tpu=True, now=sat), round(20 * 24.5 / 168, 2))

    def test_the_rate_comes_from_measured_gpu_batches_not_tpu_or_unmeasured(self):
        with tempfile.TemporaryDirectory() as d:
            old, prover.BATCHES = prover.BATCHES, Path(d) / "b.jsonl"
            try:
                self.assertEqual(prover.sec_per_sample(), prover.PRIOR_SEC_PER_SAMPLE)
                prover.BATCHES.write_text("\n".join(json.dumps(r) for r in [
                    {"batch": "b1", "ran_min": 100, "answers": 60}, {"batch": "b2", "ran_min": 50, "answers": 40},
                    {"batch": "tpu-smoke-x", "ran_min": 5, "answers": 400}, {"batch": "b3", "answers": 9}]))
                self.assertEqual(prover.sec_per_sample(), 90.0)
            finally:
                prover.BATCHES = old

    def test_the_budget_lands_in_the_gpu_kernel_and_its_stop_rule_counts_the_next_chunk(self):
        with tempfile.TemporaryDirectory() as d:
            t = {"target_set": "minif2f/test", "target": NAME, "rung": "math-L1", "order": 1}
            prover.build(d, [(t, 32)], "b9", budget_h=9.18)
            src = (Path(d) / "prover_kernel.py").read_text()
            self.assertIn("BUDGET_S = 33048", src)
            self.assertIn(f"SEC_PER_SAMPLE = {prover.sec_per_sample()}", src)
            self.assertIn("time.time() - t0 + need > BUDGET_S", src)
            compile(src, "prover_kernel.py", "exec")
            prover.build(d, [(t, 32)], "b10")                                # no budget given: the template's own
            self.assertIn("BUDGET_S = 9 * 3600", (Path(d) / "prover_kernel.py").read_text())


if __name__ == "__main__":
    unittest.main()
