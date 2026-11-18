import hashlib, json, re, sys, tempfile, unittest
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

    def test_the_scheduled_tpu_runs_the_8b_and_the_32b_only_when_asked(self):
        # 2026-10-24: two 32B batches died in loading at ~80 min; the 8B ran 640 answers in 93 min (tpu-20261020T2225)
        open_list = [{"target_set": "minif2f/test", "target": t, "rung": r, "order": i}
                     for i, (t, r) in enumerate([("a", "imo"), ("b", "custom")])]
        reach = {("minif2f/test", "a")}
        work, model, prefix = prover.tpu_work(open_list, [], [], reach, bar=False)
        self.assertEqual((prefix, model, [t["target"] for t, _ in work]), ("tpu-", None, ["a", "b"]))
        work, model, prefix = prover.tpu_work(open_list, [], [], reach, bar=False, tpu32=True)
        self.assertEqual((prefix, model, [t["target"] for t, _ in work]), ("tpu32-", prover.PROVER_32B["model"], ["a"]))
        work, _, prefix = prover.tpu_work(open_list, [], [], set(), bar=False, tpu32=True)
        self.assertEqual((prefix, work), ("tpu32-", []), "asked for the 32B, never handed the 8B instead")

    def test_a_32b_answer_is_judged_and_credited_as_the_32b(self):
        a = {**answer(0), "config": {"model": prover.PROVER_32B["model"]}}
        self.assertIs(prover.lane_for([a]), prover.PROVER_32B)
        self.assertIs(prover.lane_for([answer(0)]), prover.PROVER)
        self.assertNotEqual(prover.PROVER_32B["mode"], prover.PROVER["mode"])

    def test_a_32b_tpu_kernel_names_the_32b(self):
        with tempfile.TemporaryDirectory() as d:
            t = {"target_set": "minif2f/test", "target": NAME, "rung": "imo", "order": 1}
            prover.build(d, [(t, 32)], "tpu32-20261023T0000", tpu=True, budget_h=8.5, model=prover.PROVER_32B["model"])
            text = (Path(d) / "prover_kernel.py").read_text()
            self.assertIn('MODEL = "Goedel-LM/Goedel-Prover-V2-32B"', text)
            self.assertIn('if r.returncode == 0 else', text, "a failed import probe keeps the tail of its traceback by exit code, not by stream")
            # #534, 2026-11-04: the import is probed before the download as well, limits read on both sides, and a
            # failure after the download retried once the download's page cache is evicted
            self.assertLess(text.index('beat("probe", when="before download"'), text.index('phase = "downloading"'))
            self.assertIn('os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED)', text)
            self.assertIn('beat("probe", when="after advising the page cache away", evicted=evicted', text)
            compile(text, "prover_kernel.py", "exec")
            self.assertIn('if phase == "loading" or waited >= BEAT_S', text, "one beat a minute while vLLM loads, stepped by the minute")

    def test_a_tpu_kernel_gets_its_budget_less_the_load_and_one_chunk(self):
        with tempfile.TemporaryDirectory() as d:
            t = {"target_set": "minif2f/test", "target": NAME, "rung": "imo", "order": 1}
            prover.build(d, [(t, 32)], "tpu-20261020T2300", tpu=True, budget_h=8.5)
            src = (Path(d) / "prover_kernel.py").read_text()
            self.assertIn(f"BUDGET_S = {int((8.5 - prover.TPU_RESERVE_H) * 3600)}", src)
            self.assertEqual(json.loads((Path(d) / "kernel-metadata.json").read_text())["id"], prover.KERNEL_ID_TPU)

    def test_a_tpu_kernel_gets_its_own_random_heartbeat_topic_and_the_beats_reader_finds_it(self):
        t = {"target_set": "minif2f/test", "target": NAME, "rung": "imo", "order": 1}
        srcs = []
        for _ in range(2):
            with tempfile.TemporaryDirectory() as d:
                prover.build(d, [(t, 32)], "tpu32-20261023T0000", tpu=True, budget_h=8.5)
                srcs.append((Path(d) / "prover_kernel.py").read_text())
        (b1, t1), (b2, t2) = map(prover.kernel_fills, srcs)
        self.assertEqual((b1, b2), ("tpu32-20261023T0000",) * 2)
        self.assertTrue(t1.startswith("sparebrains-tpu32-20261023T0000-") and len(t1) > 40, t1)
        self.assertNotEqual(t1, t2, "a fresh topic per push: a leaked one never names the next batch")
        with tempfile.TemporaryDirectory() as d:
            prover.build(d, [(t, 32)], "b9")
            self.assertNotIn("NTFY_TOPIC", (Path(d) / "prover_kernel.py").read_text(), "the GPU kernel is unchanged")
        raw = (Path(prover.ROOT) / "tools" / "prover_kernel_tpu.py").read_text()
        self.assertEqual(prover.kernel_fills(raw), (None, None), "an unfilled kernel has no batch and sends nothing")

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
            (arm_dir / "rows-plan-p1-2.jsonl").write_text("".join(json.dumps(r) + "\n" for r in
                [row("b", "plan", "accept"), row("c", "alone", "accept")]))    # c's plan arm never ran
            self.assertEqual([p["target"] for p in prover.plan_owed(d, plans)["plans"]], ["c"])
            # 2026-10-30: 5 plans stayed owed for 8 days because their problems were solved by other lanes before their
            # batch; plan_work only builds open problems, so the gate (plan_owed() is None) could never open
            self.assertIsNone(prover.plan_owed(d, plans, open_keys={("minif2f/test", "a"), ("minif2f/test", "b")}))
            self.assertEqual([p["target"] for p in prover.plan_owed(d, plans, open_keys={("minif2f/test", "c")})["plans"]], ["c"])
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


class GuidedBatchTests(unittest.TestCase):
    """A gated blueprint's holes through the Kaggle prover (DECISIONS.md 2026-11-15). A guided solve is the guide's
    propositions plus the prover: its answers must never reach judge_goals, judge_plan, a Recorder, verified/ or the
    site. The only writers are the rows file in ledger/stall and the accepted text in SB_GUIDED_OUT."""
    STMTS = ["x = x", "x + 0 = x"]
    MID = "pilot-guided-kaggle-x"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.stall = self.root / "stall"
        (self.stall / "blueprints").mkdir(parents=True)
        self.bp = self.stall / "blueprints" / f"{NAME}-20261109T000000Z.json"
        self.bp.write_text(json.dumps({"ok": True, "statements": self.STMTS}))
        self.man = {"id": self.MID, "filler": "kaggle", "problems": [f"minif2f/test/{NAME}"], "samples_per_hole": 2}
        (self.stall / f"{self.MID}.json").write_text(json.dumps(self.man))
        import blueprint
        self.work = blueprint.kaggle_work(self.man, 2, read=lambda s, t: TARGET, find=lambda name: self.bp,
                                          rel=lambda path: str(path))
        self.batch = f"guided-{self.MID}-20261115T0000"

    def answers(self, texts_by_hole):
        return [{"batch": self.batch, "target_set": w["target_set"], "target": w["target"], "sample": k, "guided": w["guided"],
                 "text": text, "tokens": 10, "finish": "stop", "seconds": 1.0, "config": {"model": prover.MODEL}}
                for w in self.work for k, text in enumerate(texts_by_hole.get(w["guided"]["hole"], []))]

    GOOD = "```lean4\ntheorem sb_goal (x : ℝ) : x = x := by\n  rfl\n```"

    def judge(self, answers, verdict="accept", **kw):
        judge_text = lambda text: {"verdict": verdict, "reason": "", "output": "error"}
        return prover.judge_guided(answers, judge_text=judge_text, read=lambda s, t: TARGET, run_id="t1", stall=self.stall,
                                   guided_out=self.root / "held", closer=lambda lp: None,
                                   blueprint_at=lambda rel: Path(rel), **kw)

    def rows(self):
        return [json.loads(l) for l in (self.stall / f"{self.batch}.jsonl").read_text().splitlines()]

    def test_a_manifest_is_owed_until_its_rows_file_exists_and_only_when_it_asks_for_kaggle(self):
        self.assertEqual(prover.guided_owed(self.stall)["id"], self.MID)
        (self.stall / "pilot-router.json").write_text(json.dumps({"id": "pilot-router", "lanes": ["a"], "problems": []}))
        self.assertEqual(prover.guided_owed(self.stall)["id"], self.MID, "a router pilot (no filler) is never a Kaggle batch")
        self.judge(self.answers({1: [self.GOOD, self.GOOD], 2: [self.GOOD, self.GOOD]}))
        self.assertIsNone(prover.guided_owed(self.stall))

    def test_a_batch_mixing_guided_answers_with_any_other_kind_is_refused(self):
        a = self.answers({1: [self.GOOD]})
        self.assertEqual(prover.guided_answers(a), a)
        self.assertEqual(prover.guided_answers([answer(0)]), [])
        with self.assertRaises(SystemExit):
            prover.guided_answers(a + [answer(0)])
        with self.assertRaises(SystemExit):
            prover.guided_answers(a + [dict(answer(0), goal="abc")])

    def test_every_hole_proved_is_a_guided_accept_held_out_of_the_ledger(self):
        stats = self.judge(self.answers({1: [self.GOOD, self.GOOD], 2: [self.GOOD, self.GOOD]}))
        (row,) = self.rows()
        self.assertEqual((row["arm"], row["manifest"], row["batch"], row["final"]), ("K", self.MID, self.batch, "accept"))
        self.assertEqual(row["closed_by"], {"1": prover.BACKEND, "2": prover.BACKEND})
        self.assertEqual((row["asked"], row["answered"], row["unread"], row["truncated"]), (4, 2, 2, False))
        self.assertEqual(row["try_mode"], "guided")
        held = list((self.root / "held").glob("*.lean"))
        self.assertEqual(len(held), 1)
        self.assertEqual(row["accepted_sha"], hashlib.sha256(held[0].read_bytes()).hexdigest())
        self.assertNotIn("rfl", json.dumps(row), "the accepted text is in the artifact, the row carries its hash")
        self.assertEqual(stats["solved"], 1)
        self.assertEqual(sorted(p.name for p in self.stall.iterdir()), ["blueprints", f"{self.batch}.jsonl", f"{self.MID}.json"])

    def test_pending_is_the_whole_batch_until_the_rows_file_exists(self):
        a = self.answers({1: [self.GOOD], 2: [self.GOOD]})
        self.assertEqual(prover.guided_pending(a, self.stall), 2)
        self.judge(a)
        self.assertEqual(prover.guided_pending(a, self.stall), 0)

    def test_hint_pair_pipeline_keeps_arms_separate_and_holds_proofs_outside_ledger(self):
        import blueprint
        self.man.update(blueprint={"path": str(self.bp), "sha256": hashlib.sha256(self.bp.read_bytes()).hexdigest()},
                        target_sha256={f"minif2f/test/{NAME}": hashlib.sha256(TARGET.encode()).hexdigest()},
                        generation={"model": "fixture", "revision": "a" * 40},
                        hint_pairs={f"minif2f/test/{NAME}:{i}": ["Nat.prime_def"] for i in (1, 2)})
        (self.stall / f"{self.MID}.json").write_text(json.dumps(self.man))
        self.work = blueprint.kaggle_work(self.man, 2, read=lambda s, t: TARGET, find=lambda name: self.bp,
                                          rel=lambda path: str(path))
        answers = self.answers({1: [self.GOOD, self.GOOD], 2: [self.GOOD, self.GOOD]})
        for a in answers:
            a["config"].update(self.man["generation"])
            if a["guided"]["hint_arm"] == "unhinted":
                a["text"] = "no proof"
        stats = self.judge(answers)
        self.assertTrue(stats["complete"])
        self.assertFalse(stats["whole_proof_checked"])
        rows = self.rows()
        self.assertEqual(len(rows), 2)
        self.assertTrue(all(r["arms"]["hinted"]["pass_at_n"] for r in rows))
        self.assertFalse(any(r["arms"]["unhinted"]["pass_at_n"] for r in rows))
        self.assertNotIn("rfl", json.dumps(rows))
        self.assertEqual(len(list((self.root / "held").glob("hint-proofs-*.json"))), 1)
        self.assertIsNone(prover.guided_owed(self.stall))

    def test_a_blueprint_or_target_changed_since_export_judges_nothing(self):
        a = self.answers({1: [self.GOOD], 2: [self.GOOD]})
        self.bp.write_text(json.dumps({"ok": True, "statements": ["x = x", "True"]}))
        self.judge(a)
        (row,) = self.rows()
        self.assertIn("changed since export", row["note"])
        self.assertNotIn("final", row)
        self.assertFalse((self.root / "held").exists())

    def test_answers_from_another_manifest_or_a_batch_named_for_another_are_refused(self):
        a = self.answers({1: [self.GOOD]})
        with self.assertRaises(SystemExit):
            self.judge([dict(a[0], batch="guided-pilot-other-20261115T0000")])
        with self.assertRaises(SystemExit):
            self.judge(a + [dict(a[0], guided=dict(a[0]["guided"], manifest="pilot-other"))])

    def held(self, batch=None):
        return self.root / "held" / f"holes-{batch or self.batch}.json"

    def test_every_closed_holes_proof_is_held_beside_the_accept_and_the_row_carries_its_hash(self):
        """2026-11-16: the first batch closed holes 2 and 4 and their proofs were kept nowhere a second batch could
        read. Held with the accepted text (the artifact), never in the ledger: the hole bodies together are the solve."""
        judge_text = lambda text: {"verdict": "accept" if "x + 0 = x := by" in text and "have bp_" not in text else "reject",
                                   "reason": "", "output": ""}
        prover.judge_guided(self.answers({1: [self.GOOD, self.GOOD], 2: [self.GOOD, self.GOOD]}), judge_text=judge_text,
                            read=lambda s, t: TARGET, run_id="t1", stall=self.stall, guided_out=self.root / "held",
                            closer=lambda lp: None, blueprint_at=lambda rel: Path(rel))
        (row,) = self.rows()
        doc = json.loads(self.held().read_text())
        hole = doc["problems"][f"minif2f/test/{NAME}"]["holes"]
        self.assertEqual(hole, {"2": {"by": prover.BACKEND, "batch": self.batch, "lines": ["rfl"], "sample": 0, "repaired": False}})
        self.assertEqual(row["hole_sha"], {"2": hashlib.sha256(b"rfl").hexdigest()})
        self.assertEqual(row["holes_file_sha"], hashlib.sha256(self.held().read_bytes()).hexdigest())
        self.assertNotIn("rfl", json.dumps(row))
        self.assertEqual(sorted(p.name for p in self.stall.iterdir()), ["blueprints", f"{self.batch}.jsonl", f"{self.MID}.json"])

    def continuing(self, first_holes, sha=None, tag="b"):
        """A second manifest that carries `first_holes` from self.batch and samples hole 1 only."""
        g = self.work[0]["guided"]
        text = json.dumps({"batch": self.batch, "problems": {f"minif2f/test/{NAME}": {
            "blueprint_sha": g["blueprint_sha"], "target_sha": g["target_sha"], "holes": first_holes}}})
        (self.root / "in").mkdir(exist_ok=True)
        (self.root / "in" / f"holes-{self.batch}.json").write_text(text)
        mid = self.MID + "-" + tag
        man = {"id": mid, "filler": "kaggle", "problems": [f"minif2f/test/{NAME}"], "samples_per_hole": 2, "holes": [1],
               "carry": {"batch": self.batch, "run": 7, "artifact": "a", "sha256": sha or hashlib.sha256(text.encode()).hexdigest()}}
        (self.stall / f"{mid}.json").write_text(json.dumps(man))
        import blueprint
        work = blueprint.kaggle_work(man, 2, read=lambda s, t: TARGET, find=lambda name: self.bp, rel=lambda path: str(path))
        batch = f"guided-{mid}-20261116T0000"
        answers = [{"batch": batch, "target_set": w["target_set"], "target": w["target"], "sample": k, "guided": w["guided"],
                    "text": self.GOOD, "config": {"model": prover.MODEL}} for w in work for k in range(2)]
        stats = prover.judge_guided(answers, judge_text=lambda text: {"verdict": "reject" if "stale" in text else "accept",
                                                                      "reason": "", "output": ""},
                                    read=lambda s, t: TARGET, run_id="t2", stall=self.stall, guided_out=self.root / "held",
                                    guided_in=self.root / "in", closer=lambda lp: None, blueprint_at=lambda rel: Path(rel))
        (row,) = [json.loads(l) for l in (self.stall / f"{batch}.jsonl").read_text().splitlines()]
        return row, stats, batch

    FIRST = {"2": {"by": "kaggle-goedel-prover-v2-8b", "batch": "first", "lines": ["simp"], "sample": 3, "repaired": True}}

    def test_a_second_batch_carries_the_first_batchs_hole_and_credits_its_first_closer(self):
        row, stats, batch = self.continuing(self.FIRST)
        self.assertEqual(row["closed_by"], {"1": prover.BACKEND, "2": f"carried:{self.batch}"})
        self.assertEqual(row["carried_from"], {"2": "kaggle-goedel-prover-v2-8b+chain"}, "never the second batch's samples")
        self.assertEqual((stats["closed_by_prover"], stats["carried"]), (1, 1), "the summary line does not count a carried hole as this batch's")
        self.assertEqual((row["planned"], row["generated"], row["truncated"]), ({"1": 2, "2": 0}, {"1": 2, "2": 0}, False))
        self.assertEqual((row["final"], row["carry_missing"], row["carry_failed"]), ("accept", None, []))
        hole = json.loads(self.held(batch).read_text())["problems"][f"minif2f/test/{NAME}"]["holes"]
        self.assertEqual(hole["2"], self.FIRST["2"], "the cumulative file keeps who first proved a carried hole")
        self.assertEqual((hole["1"]["by"], hole["1"]["batch"]), (prover.BACKEND, batch))

    def test_a_carry_that_is_missing_altered_or_stale_leaves_the_hole_open_and_says_why(self):
        row, _, _ = self.continuing(self.FIRST, sha="0" * 64)
        self.assertEqual((row["closed_by"], row["unattempted"]), ({"1": prover.BACKEND}, [2]))
        self.assertIn("not the bytes the manifest froze", row["carry_missing"])
        self.assertIsNone(row["final"], "an open hole: not checked")
        row, _, _ = self.continuing({"2": dict(self.FIRST["2"], lines=["stale"])}, tag="c")
        self.assertEqual((row["carry_failed"], row["unattempted"], row["carry_missing"]), ([2], [2], None))

    def with_sub(self, tag, reject=None, keep=lambda a: True):
        """A manifest whose hole 1 has a blueprint of its own (two holes); hole 2 is sampled whole."""
        import blueprint
        g = self.work[0]["guided"]
        sp = self.stall / "blueprints" / f"{NAME}.bp1-x.json"
        sp.write_text(json.dumps({"ok": True, "statements": ["x * 1 = x", "x = x * 1"], "parent_sha": g["blueprint_sha"],
                                  "hole": 1, "final": "grind"}))
        mid = f"{self.MID}-{tag}"
        man = {"id": mid, "filler": "kaggle", "problems": [f"minif2f/test/{NAME}"], "samples_per_hole": 2, "holes": [2],
               "sub": {f"minif2f/test/{NAME}": {"hole": 1, "blueprint": str(sp), "sha256": hashlib.sha256(sp.read_bytes()).hexdigest()}}}
        (self.stall / f"{mid}.json").write_text(json.dumps(man))
        work = blueprint.kaggle_work(man, 2, read=lambda s, t: TARGET, find=lambda name: self.bp, rel=lambda path: str(path),
                                     at=lambda r: Path(r))
        batch = f"guided-{mid}-20261116T0000"
        answers = [{"batch": batch, "target_set": w["target_set"], "target": w["target"], "sample": k, "guided": w["guided"],
                    "text": self.GOOD, "config": {"model": prover.MODEL}} for w in work for k in range(2)]
        answers = [a for a in answers if keep(a)]
        judge_text = lambda text: {"verdict": "reject" if reject and reject in text else "accept", "reason": "", "output": ""}
        self.stats = prover.judge_guided(answers, judge_text=judge_text, read=lambda s, t: TARGET, run_id="t3", stall=self.stall,
                            guided_out=self.root / "held", closer=lambda lp: None, blueprint_at=lambda rel: Path(rel))
        (row,) = [json.loads(l) for l in (self.stall / f"{batch}.jsonl").read_text().splitlines()]
        return row, json.loads(self.held(batch).read_text())["problems"][f"minif2f/test/{NAME}"], batch

    def test_a_holes_own_blueprint_proved_whole_is_that_holes_body_and_is_credited_as_such(self):
        row, kept, batch = self.with_sub("s")
        self.assertEqual(row["closed_by"], {"1": "sub-blueprint", "2": prover.BACKEND})
        self.assertEqual((row["subs"][0]["closed_by"], row["subs"][0]["final"]), ({"1": prover.BACKEND, "2": prover.BACKEND}, "accept"))
        self.assertEqual((row["planned"], row["subs"][0]["planned"], row["final"]), ({"1": 0, "2": 2}, {"1": 2, "2": 2}, "accept"))
        self.assertEqual(kept["holes"]["1"]["by"], "sub-blueprint")
        self.assertEqual(kept["holes"]["1"]["lines"], ["have bp_1 : x * 1 = x := by", "  rfl", "have bp_2 : x = x * 1 := by", "  rfl", "grind"],
                         "the sub-blueprint's own closing line, dedented to the hole")
        self.assertEqual(sorted(kept["subs"][0]["holes"]), ["1", "2"])
        held = (self.root / "held" / f"{NAME}-{batch}.lean").read_text()
        self.assertIn("  have bp_1 : x = x := by\n    have bp_1 : x * 1 = x := by\n      rfl\n", held)

    def test_a_budget_cut_before_the_first_sub_answer_still_records_the_subs_coverage_as_truncated(self):
        """Codex 20261116T055155373979Z f2: the kernel's fit_chunk returned parent hole 3 alone with eight samples'
        time left; with the child's coverage read from the answers, the row said nothing was cut."""
        row, kept, _ = self.with_sub("u", keep=lambda a: not a["guided"].get("path"))
        self.assertEqual((row["subs"][0]["planned"], row["subs"][0]["generated"]), ({"1": 2, "2": 2}, {"1": 0, "2": 0}))
        self.assertEqual((row["subs"][0]["truncated"], row["subs"][0]["unattempted"], self.stats["truncated"]), (True, [1, 2], 1))
        self.assertEqual((row["closed_by"], row["unattempted"], row["final"]), ({"2": prover.BACKEND}, [1], None))
        self.assertEqual(row["guide_rounds"], 2)

    def test_a_holes_own_blueprint_left_open_leaves_the_hole_open_and_keeps_what_it_closed(self):
        row, kept, _ = self.with_sub("t", reject="(bp_1 : x * 1 = x) : x = x * 1 := by")
        self.assertEqual((row["closed_by"], row["unattempted"], row["final"]), ({"2": prover.BACKEND}, [1], None))
        self.assertEqual((row["subs"][0]["closed_by"], row["subs"][0]["failed"], row["subs"][0]["final"]), ({"1": prover.BACKEND}, [2], None))
        self.assertEqual((sorted(kept["holes"]), sorted(kept["subs"][0]["holes"])), (["2"], ["1"]))

    def tree(self, tag, reject=None, first=None):
        """Hole 1 has a blueprint (two holes) whose hole 2 has one in turn (bq_1, bq_2); hole 2 has one too (bq_1)."""
        import blueprint
        g, key = self.work[0]["guided"], f"minif2f/test/{NAME}"
        d = self.stall / "blueprints"
        put = lambda name, doc: ((d / name).write_text(json.dumps(doc)), {
            "hole": doc["hole"], "blueprint": str(d / name), "sha256": hashlib.sha256((d / name).read_bytes()).hexdigest()})[1]
        one = put(f"{NAME}.bp1-x.json", {"ok": True, "statements": ["x * 1 = x", "x = x * 1"], "parent_sha": g["blueprint_sha"], "hole": 1})
        deep = put(f"{NAME}.bp1_2-x.json", {"ok": True, "statements": ["x * 1 = x * 1", "x * 1 * 1 = x"], "parent_sha": one["sha256"],
                                           "hole": 2, "stem": "bq"})
        two = put(f"{NAME}.bp2-x.json", {"ok": True, "statements": ["x + 0 + 0 = x"], "parent_sha": g["blueprint_sha"], "hole": 2,
                                        "stem": "bq"})
        mid = f"{self.MID}-{tag}"
        man = {"id": mid, "filler": "kaggle", "problems": [key], "samples_per_hole": 2, "holes": [],
               "subs": {key: [{**one, "holes": [1], "subs": [deep]}, two]}}
        if first:
            text = json.dumps({"batch": self.batch, "problems": {key: {"blueprint_sha": g["blueprint_sha"], "target_sha": g["target_sha"],
                                                                         "holes": {}, **first(one)}}})
            (self.root / "in").mkdir(exist_ok=True)
            (self.root / "in" / f"holes-{self.batch}.json").write_text(text)
            man["carry"] = {"batch": self.batch, "run": 7, "artifact": "a", "sha256": hashlib.sha256(text.encode()).hexdigest()}
        (self.stall / f"{mid}.json").write_text(json.dumps(man))
        work = blueprint.kaggle_work(man, 2, read=lambda s, t: TARGET, find=lambda name: self.bp, rel=lambda path: str(path),
                                     at=lambda r: Path(r))
        batch = f"guided-{mid}-20261116T0000"
        answers = [{"batch": batch, "target_set": w["target_set"], "target": w["target"], "sample": k, "guided": w["guided"],
                    "text": self.GOOD, "config": {"model": prover.MODEL}} for w in work for k in range(2)]
        judge_text = lambda text: {"verdict": "reject" if reject and reject in text else "accept", "reason": "", "output": ""}
        self.stats = prover.judge_guided(answers, judge_text=judge_text, read=lambda s, t: TARGET, run_id="t4", stall=self.stall,
                            guided_out=self.root / "held", guided_in=self.root / "in", closer=lambda lp: None,
                            blueprint_at=lambda rel: Path(rel))
        (row,) = [json.loads(l) for l in (self.stall / f"{batch}.jsonl").read_text().splitlines()]
        return row, json.loads(self.held(batch).read_text())["problems"][key], work, batch

    def test_a_hole_of_a_holes_blueprint_can_have_a_blueprint_too_and_every_level_is_read_apart(self):
        """2026-11-16: the second batch left sub-holes 2, 3, 5 of hole 1 and hole 3 open after 8 and 16 samples; with one
        blueprint per problem, for hole 1 only, none of them could be split again."""
        row, kept, work, batch = self.tree("n")
        self.assertEqual([(w["guided"]["path"], w["guided"]["hole"]) for w in work],
                         [([1], 1), ([1, 2], 1), ([1, 2], 2), ([2], 1)], "no hole with a blueprint is sampled whole")
        self.assertTrue(work[2]["statement"].endswith(
            "theorem sb_goal (x : ℝ) (bp_1 : x * 1 = x) (bq_1 : x * 1 = x * 1) : x * 1 * 1 = x := by\n  sorry\n"), work[2]["statement"][-110:])
        self.assertTrue(work[3]["statement"].endswith("theorem sb_goal (x : ℝ) (bp_1 : x = x) : x + 0 + 0 = x := by\n  sorry\n"))
        self.assertEqual((row["closed_by"], row["final"], row["guide_rounds"]), ({"1": "sub-blueprint", "2": "sub-blueprint"}, "accept", 3))
        self.assertEqual([(r["path"], r["closed_by"], r["final"]) for r in row["subs"]],
                         [([1], {"1": prover.BACKEND, "2": "sub-blueprint"}, "accept"),
                          ([1, 2], {"1": prover.BACKEND, "2": prover.BACKEND}, "accept"), ([2], {"1": prover.BACKEND}, "accept")])
        self.assertEqual(self.stats["closed_by_sub_blueprint"], 2)
        self.assertEqual(sorted(kept["subs"][0]["subs"][0]["holes"]), ["1", "2"])
        held = (self.root / "held" / f"{NAME}-{batch}.lean").read_text()
        self.assertIn("    have bp_2 : x = x * 1 := by\n      have bq_1 : x * 1 = x * 1 := by\n        rfl\n", held)

    def test_a_deep_blueprint_left_open_leaves_every_hole_above_it_open(self):
        row, kept, _, _ = self.tree("o", reject="(bq_1 : x * 1 = x * 1) : x * 1 * 1 = x := by")
        self.assertEqual((row["closed_by"], row["unattempted"], row["final"]), ({"2": "sub-blueprint"}, [1], None))
        self.assertEqual([(r["path"], r["closed_by"], r["failed"], r["unattempted"]) for r in row["subs"]],
                         [([1], {"1": prover.BACKEND}, [], [2]), ([1, 2], {"1": prover.BACKEND}, [2], []), ([2], {"1": prover.BACKEND}, [], [])])
        self.assertEqual(sorted(kept["subs"][0]["subs"][0]["holes"]), ["1"], "what closed is held for the next batch")

    def test_holes_held_in_the_first_form_of_the_file_are_carried_into_a_tree(self):
        """Run 43917149539's artifact holds hole 1's blueprint as `sub`, one node; the next manifest carries from it."""
        first = lambda one: {"sub": {"hole": 1, "blueprint_sha": one["sha256"], "holes": {
            "1": {"by": "kaggle-goedel-prover-v2-8b", "batch": "first", "lines": ["simp"], "sample": 0, "repaired": False}}}}
        row, kept, work, _ = self.tree("p", first=first)
        self.assertEqual([w["guided"]["path"] for w in work], [[1], [1, 2], [1, 2], [2]])
        one = row["subs"][0]
        self.assertEqual((one["closed_by"]["1"], one["carried_from"]), (f"carried:{self.batch}", {"1": "kaggle-goedel-prover-v2-8b"}))
        self.assertEqual(kept["subs"][0]["holes"]["1"]["batch"], "first")
        self.assertEqual(row["final"], "accept")

    def test_judging_a_batch_again_writes_its_holes_file_and_leaves_the_committed_row_alone(self):
        """The backfill for the batch judged before holes were kept (workflow input `rejudge`)."""
        a = self.answers({1: [self.GOOD, self.GOOD], 2: [self.GOOD, self.GOOD]})
        self.judge(a, verdict="reject")
        before = (self.stall / f"{self.batch}.jsonl").read_bytes()
        self.assertFalse(self.held().exists())
        stats = self.judge(a)
        self.assertEqual((self.stall / f"{self.batch}.jsonl").read_bytes(), before)
        self.assertEqual(stats["holes_kept"], {f"minif2f/test/{NAME}": [1, 2]})
        self.assertTrue(stats["rejudged_for_holes_only"])
        self.assertEqual(sorted(json.loads(self.held().read_text())["problems"][f"minif2f/test/{NAME}"]["holes"]), ["1", "2"])

    def test_a_truncated_batch_is_recorded_incomplete_with_coverage_by_hole(self):
        self.judge(self.answers({1: [self.GOOD]}), verdict="reject")
        (row,) = self.rows()
        self.assertEqual((row["planned"], row["generated"]), ({"1": 2, "2": 2}, {"1": 1, "2": 0}))
        self.assertEqual((row["failed"], row["unattempted"], row["truncated"]), ([1], [2], True))
        self.assertEqual((row["judge_unfinished"], row["judging_complete"]), ([], True), "generation cut short is its own flag")

    def test_a_judge_timeout_is_recorded_as_unfinished_judging_and_the_batch_is_not_owed_again(self):
        """Codex 20261116T000117894936Z f3: unfinished judging must not read as a finished failure, and must not by
        itself spend another GPU push."""
        a = self.answers({1: [self.GOOD, self.GOOD], 2: [self.GOOD, self.GOOD]})
        timeout = lambda text: {"verdict": "reject", "reason": "timeout after 300s", "output": ""}
        stats = prover.judge_guided(a, judge_text=timeout, read=lambda s, t: TARGET, run_id="t1", stall=self.stall,
                                    guided_out=self.root / "held", closer=lambda lp: None, blueprint_at=lambda rel: Path(rel))
        (row,) = self.rows()
        self.assertEqual((row["judge_unfinished"], row["failed"], row["judging_complete"]), ([1, 2], [], False))
        self.assertEqual(stats["judging_unfinished"], 1)
        self.assertIsNone(prover.guided_owed(self.stall))

    def test_the_kernel_echoes_the_guided_field_and_a_guided_batch_goes_before_any_other_kind(self):
        src = (Path(prover.__file__).parent / "prover_kernel.py").read_text()
        self.assertIn('**({"guided": p["guided"]} if p.get("guided") else {})', src)
        self.assertEqual(prover.guided_batch_name(self.MID, datetime(2026, 11, 15, tzinfo=timezone.utc)), self.batch)
        with tempfile.TemporaryDirectory() as out:
            n = prover.build(out, None, self.batch, problems=self.work)
            built = (Path(out) / "prover_kernel.py").read_text()
        self.assertEqual(n, 2)
        self.assertIn('"guided": {"manifest": "' + self.MID, built)


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
            self.assertIn("chunk = fit_chunk(full, per_sample, time.time() - t0, BUDGET_S)", src)
            compile(src, "prover_kernel.py", "exec")
            prover.build(d, [(t, 32)], "b10")                                # no budget given: the template's own
            self.assertIn("BUDGET_S = 9 * 3600", (Path(d) / "prover_kernel.py").read_text())


class KernelFit(unittest.TestCase):
    """prover_kernel.fit_chunk, read out of the kernel's source (the kernel itself installs vllm when run)."""

    def setUp(self):
        import ast
        src = (Path(prover.ROOT) / "tools" / "prover_kernel.py").read_text()
        fn = next(n for n in ast.parse(src).body if isinstance(n, ast.FunctionDef) and n.name == "fit_chunk")
        ns = {}
        exec(compile(ast.Module(body=[fn], type_ignores=[]), "prover_kernel.py", "exec"), ns)
        self.fit = ns["fit_chunk"]

    def test_batch_20261103T1804_runs_its_first_problem_instead_of_nothing(self):
        chunk = [{"target": "a", "n": 28}, {"target": "b", "n": 28}]         # 56 samples at 150.2 s: 8411 s
        got = self.fit(chunk, 150.2, 632.5, 7200)                          # 6567.5 s left: 43 samples
        self.assertEqual(got, [{"target": "a", "n": 28}, {"target": "b", "n": 15}])

    def test_a_chunk_that_fits_runs_whole_and_none_when_not_one_sample_fits(self):
        chunk = [{"target": "a", "n": 2}, {"target": "b", "n": 2}]
        self.assertIs(self.fit(chunk, 100, 0, 400), chunk)
        self.assertIsNone(self.fit(chunk, 100, 350, 400))
        self.assertEqual(self.fit([{"target": "a", "n": 1}], 100, 0, 50), None)

    def test_hint_comparison_never_trims_away_one_arm(self):
        chunk = [{"target_set": "test", "target": "a", "n": 8,
                  "guided": {"hint_arm": arm, "path": [1, 3], "hole": 2}} for arm in ("unhinted", "hinted")]
        self.assertIsNone(self.fit(chunk, 100, 0, 1200))
        self.assertIs(self.fit(chunk, 100, 0, 1600), chunk)
        with self.assertRaises(ValueError):
            self.fit(chunk[:1], 100, 0, 1600)



class TpuLimits(unittest.TestCase):
    """prover_kernel_tpu.limits(), read out of the kernel's source: bounded however long the mount options are
    (Codex 2026-11-04 f1), so a probe beat keeps its fields under the 3,900-byte cap."""

    def test_an_overlay_with_fifty_layers_stays_small_and_says_noexec(self):
        import ast, io
        from unittest import mock
        src = (Path(prover.ROOT) / "tools" / "prover_kernel_tpu.py").read_text()
        fn = next(n for n in ast.parse(src).body if isinstance(n, ast.FunctionDef) and n.name == "limits")
        ns = {}
        exec(compile(ast.Module(body=[fn], type_ignores=[]), "k.py", "exec"), ns)
        opts = "rw,lowerdir=" + ":".join(f"/var/lib/layer{i}/diff" for i in range(50)) + ",relatime"
        files = {"/proc/mounts": f"overlay / overlay {opts} 0 0\ntmpfs /tmp tmpfs rw,nosuid,noexec 0 0\n",
                 "/proc/meminfo": "CommitLimit: 1 kB\nCommitted_AS: 2 kB\nMemAvailable: 3 kB\nCached: 4 kB\n"}
        real = open
        fake = lambda path, *a, **k: io.StringIO(files.get(path, "0\n")) if str(path).startswith("/proc") else real(path, *a, **k)
        with mock.patch("builtins.open", fake):
            out = ns["limits"]()
        self.assertLess(len(json.dumps(out)), 900)
        self.assertEqual((out["mounts"]["/"]["noexec"], out["mounts"]["/tmp"]["noexec"]), (False, True))
        self.assertEqual(out["CommitLimit"], "1 kB")

    def test_a_probe_beat_with_an_escaped_traceback_keeps_its_diagnostics_under_the_cap(self):
        import ast
        from unittest import mock
        src = (Path(prover.ROOT) / "tools" / "prover_kernel_tpu.py").read_text()
        fn = next(n for n in ast.parse(src).body if isinstance(n, ast.FunctionDef) and n.name == "_beat")
        sent = []

        class U:
            Request = staticmethod(lambda url, data=None, headers=None: data)
            urlopen = staticmethod(lambda data, timeout=None: sent.append(data))
        ns = {"json": json, "time": __import__("time"), "os": __import__("os"), "shutil": __import__("shutil"),
              "urllib": type("M", (), {"request": U}), "BATCH": "b", "phase": "downloading", "T_START": 0,
              "DISKS": (), "NTFY_TOPIC": "t", "memory": lambda: {"current": 1}}
        exec(compile(ast.Module(body=[fn], type_ignores=[]), "k.py", "exec"), ns)
        trace = "Traceback\n" + "  File \"/tmp/ü/é.py\" ✓\n" * 120 + "ImportError: libstdc++.so.6: failed to map segment"
        lim = {"CommitLimit": "1 kB", "mounts": {"/tmp": {"noexec": False}}}
        ns["_beat"]("probe", when="after advising the page cache away", evicted={"ok": 20, "failed": 3},
                    versions="import failed (exit 1): " + trace, limits=lim)
        body = json.loads(sent[0])
        self.assertLessEqual(len(sent[0]), 3900)
        self.assertEqual((body["evicted"], body["limits"], body["when"]), ({"ok": 20, "failed": 3}, lim, "after advising the page cache away"))
        self.assertTrue(body["versions"].endswith("failed to map segment"), "the traceback keeps its last line")


class RecorderOrder(unittest.TestCase):
    """Codex 20261105 publish f1: the ledger row went first, so a job killed before verified/ was written left an accept
    that every later call skipped as done, and the proof was never published."""
    def test_an_accepted_proof_is_on_disk_before_its_ledger_row(self):
        import tempfile
        from unittest import mock
        with tempfile.TemporaryDirectory() as d, mock.patch.object(prover, "ROOT", Path(d)):
            rec = prover.Recorder("b", None, prover.PROVER)
            row = {"target_set": "minif2f/test", "target": "t", "verdict": "accept"}
            (Path(d) / "ledger").write_text("not a directory")       # the ledger write fails, as a kill would
            with self.assertRaises(OSError):
                rec(row, "text", "proof", "theorem t : True := trivial", "")
            out = Path(d) / "verified" / "minif2f/test" / "t" / f"{prover.PROVER['backend']}.lean"
            self.assertEqual(out.read_text(), "theorem t : True := trivial")

    def test_a_rewrite_killed_half_way_keeps_the_proof(self):   # Codex 20261105T212508667868Z f1
        import os, tempfile
        from unittest import mock
        with tempfile.TemporaryDirectory() as d, mock.patch.object(prover, "ROOT", Path(d)):
            rec = prover.Recorder("b", None, prover.PROVER)
            rec.verified("s", "t", "proof one")
            out = Path(d) / "verified" / "s" / "t" / f"{prover.PROVER['backend']}.lean"
            with mock.patch.object(os, "replace", side_effect=KeyboardInterrupt):
                with self.assertRaises(KeyboardInterrupt):
                    rec.verified("s", "t", "proof two")
            self.assertEqual(out.read_text(), "proof one", "the old proof is intact, never truncated")
            self.assertEqual([p.name for p in Path(d).glob(".verified-*")], [], "no partial left")
            with mock.patch.object(os, "replace", side_effect=AssertionError("a same-text rewrite must not write")):
                rec.verified("s", "t", "proof one")

    def test_a_reject_writes_no_proof(self):
        import tempfile
        from unittest import mock
        with tempfile.TemporaryDirectory() as d, mock.patch.object(prover, "ROOT", Path(d)):
            prover.Recorder("b", None, prover.PROVER)({"target_set": "s", "target": "t", "verdict": "reject"}, "", "", "c", "")
            self.assertFalse((Path(d) / "verified").exists())


if __name__ == "__main__":
    unittest.main()


class HeartbeatTests(unittest.TestCase):
    """A TPU batch's heartbeats (2026-10-23): kept from ntfy into ledger/prover-beats/, each once, ours only."""

    @staticmethod
    def ev(i, t, body):
        return json.dumps({"id": i, "time": t, "event": "message", "topic": "x",
                           "message": body if isinstance(body, str) else json.dumps(body)})

    def test_beats_are_kept_once_in_order_and_strangers_are_dropped(self):
        b = "tpu32-20261023T0000"
        polled = "\n".join([
            self.ev("c", 30, {"batch": b, "event": "alive", "phase": "loading"}),
            self.ev("a", 10, {"batch": b, "event": "started", "phase": "started"}),
            self.ev("x", 15, {"batch": "tpu-other", "event": "finished"}),        # someone else's batch name
            self.ev("y", 16, "hello from a stranger"),                              # not our JSON
            json.dumps({"id": "o", "time": 5, "event": "open", "topic": "x"}),      # ntfy's own events
            "not json at all"])
        kept = prover.merge_beats([], polled, b)
        self.assertEqual([x["id"] for x in kept], ["a", "c"])
        again = prover.merge_beats(kept, polled + "\n" + self.ev("d", 40, {"batch": b, "event": "failed", "exit": -9}), b)
        self.assertEqual([x["id"] for x in again], ["a", "c", "d"], "a repeated poll adds only what is new")
        self.assertEqual(again[-1]["exit"], -9)

    def test_save_beats_writes_the_batch_file_and_skips_a_kernel_without_a_topic(self):
        old = prover.BEATS
        with tempfile.TemporaryDirectory() as d:
            prover.BEATS = Path(d) / "prover-beats"
            try:
                k = Path(d) / "k"
                k.mkdir()
                (k / "prover_kernel.py").write_text('BATCH = "tpu-20261023T0100"   # c\nNTFY_TOPIC = "sb-t-1"   # c\n')
                asked = []
                fetch = lambda topic: asked.append(topic) or self.ev("a", 1, {"batch": "tpu-20261023T0100", "event": "started"})
                batch, beats = prover.save_beats(k, fetch)
                self.assertEqual((batch, asked, len(beats)), ("tpu-20261023T0100", ["sb-t-1"], 1))
                f = prover.BEATS / "tpu-20261023T0100.jsonl"
                first = f.read_bytes()
                self.assertEqual(json.loads(first)["event"], "started")
                fetch = lambda topic: "\n".join([self.ev("a", 1, {"batch": "tpu-20261023T0100", "event": "started"}),
                                                 self.ev("b", 2, {"batch": "tpu-20261023T0100", "event": "alive"})])
                batch, beats = prover.save_beats(k, fetch)
                self.assertEqual([b["id"] for b in beats], ["a", "b"])
                self.assertTrue(f.read_bytes().startswith(first), "only appended to, so publish.py merges a later poll")
                self.assertEqual(len(f.read_text().splitlines()), 2)
                (k / "prover_kernel.py").write_text('BATCH = "tpu-20261020T2225"\nMODEL = "x"\n')   # pushed before heartbeats
                self.assertIsNone(prover.save_beats(k, fetch))
            finally:
                prover.BEATS = old


class FailedBatchTests(unittest.TestCase):
    """A batch that ended without completing alerts once (2026-10-24): the first job to see it records it in
    ledger/prover-beats/failed.jsonl with whatever log Kaggle kept, and fails; every later job sees it recorded."""

    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.root = Path(self.d.name)
        self.ledger = self.root / "failed.jsonl"
        (self.root / "kpull").mkdir()
        (self.root / "kpull" / "k.py").write_text('BATCH = "tpu32-20261023T1659"   # filled by tools/prover.py\n')
        (self.root / "kout").mkdir()

    def tearDown(self):
        self.d.cleanup()

    def fail(self, status="KernelWorkerStatus.ERROR"):
        return prover.record_failure(self.root / "kpull", self.root / "kout", status, FRI_NIGHT, "https://run/1",
                                     path=self.ledger)

    def test_a_new_failure_is_recorded_once_and_a_known_one_is_not_again(self):
        new, rec = self.fail()
        self.assertTrue(new)
        self.assertEqual((rec["batch"], rec["status"]), ("tpu32-20261023T1659", "KernelWorkerStatus.ERROR"))
        self.assertIsNone(rec["log_tail"], "Kaggle kept no log for this session: recorded as none, not as empty text")
        new, rec = self.fail()
        self.assertFalse(new)
        self.assertEqual(len(self.ledger.read_text().splitlines()), 1)

    def test_the_log_tail_is_kept_when_kaggle_has_one(self):
        (self.root / "kout" / "sparebrains-prover-tpu.log").write_text("".join(f"line {i}\n" for i in range(100)))
        _, rec = self.fail()
        self.assertEqual(rec["log_tail"].splitlines()[-1], "line 99")
        self.assertEqual(len(rec["log_tail"].splitlines()), prover.LOG_TAIL)

    def test_nothing_is_recorded_without_a_batch_id_or_a_fetched_log(self):
        # Codex 20261024T134819429956Z: an "unknown" record or a failed download would spend the batch's one alert
        (self.root / "kpull" / "k.py").write_text("print('no batch line')\n")
        self.assertIsNone(self.fail())
        self.assertFalse(self.ledger.exists())
        for args, why in ((["--dir", str(self.root / "kpull")], "no batch id"),
                          (["--dir", str(self.root / "nopull")], "no source at all")):
            self.assertEqual(self.cli(*args), 2, why)
        (self.root / "kpull" / "k.py").write_text('BATCH = "tpu32-20261023T1659"\n')
        self.assertEqual(self.cli("--dir", str(self.root / "kpull"), "--log-fetch-failed"), 2)
        self.assertFalse(self.ledger.exists(), "a failed download is retried by the next job, not recorded as no log")
        self.assertEqual(self.cli("--dir", str(self.root / "kpull")), prover.FAILED_NEW)

    def cli(self, *extra):
        old = sys.argv
        try:
            sys.argv = ["prover.py", "failed", "--out", str(self.root / "kout"), "--status", "KernelWorkerStatus.ERROR",
                        "--ledger", str(self.ledger), *extra]
            return prover.main()
        finally:
            sys.argv = old

    def test_the_cli_exits_1_on_a_new_failure_and_0_on_a_known_one(self):
        argv = ["prover.py", "failed", "--dir", str(self.root / "kpull"), "--out", str(self.root / "kout"),
                "--status", "KernelWorkerStatus.ERROR", "--ledger", str(self.ledger)]
        old = sys.argv
        try:
            sys.argv = argv
            self.assertEqual(prover.main(), prover.FAILED_NEW, "not 1: an uncaught exception exits 1 too")
            self.assertEqual(prover.main(), 0)
        finally:
            sys.argv = old


class HoldReasonTests(unittest.TestCase):
    """A held batch says what holds it (2026-10-24: 5.72 of 30 h used and held by the pace line, while the log
    said 'too little gpu quota left this week')."""

    def test_the_pace_line_and_the_quota_are_told_apart(self):
        sat_noon = datetime(2026, 10, 24, 12, 56, tzinfo=timezone.utc)
        self.assertEqual(prover.batch_hours(30, 5.72, now=sat_noon), 0.0)
        self.assertIn("pace line", prover.hold_reason(30, 5.72, now=sat_noon))
        self.assertIn("quota", prover.hold_reason(30, 29.5, now=FRI_NIGHT))
        self.assertIsNone(prover.hold_reason(30, 0.0, now=FRI_NIGHT))


class ReplacementReservationTests(unittest.TestCase):
    """One 8B replacement per failed 32B batch, by our own ledger (2026-10-24, Codex 20261024T142004542959Z): a
    reservation line goes into failed.jsonl, published and confirmed on main, before the push; never twice."""

    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.ledger = Path(self.d.name) / "failed.jsonl"
        k = Path(self.d.name) / "kpull"
        k.mkdir()
        (k / "k.py").write_text('BATCH = "tpu32-20261023T1659"\n')
        self.new, _ = prover.record_failure(k, Path(self.d.name), "KernelWorkerStatus.ERROR", FRI_NIGHT, path=self.ledger)
        self.k = k

    def tearDown(self):
        self.d.cleanup()

    def test_a_batch_is_reserved_once(self):
        self.assertFalse(prover.replacement_reserved("tpu32-20261023T1659", self.ledger))
        self.assertTrue(prover.reserve_replacement("tpu32-20261023T1659", FRI_NIGHT, "https://run/2", self.ledger))
        self.assertTrue(prover.replacement_reserved("tpu32-20261023T1659", self.ledger))
        self.assertFalse(prover.reserve_replacement("tpu32-20261023T1659", FRI_NIGHT, "https://run/3", self.ledger))
        self.assertFalse(prover.replacement_reserved("tpu32-other", self.ledger))

    def test_a_reservation_line_never_reads_as_the_failure_record(self):
        prover.reserve_replacement("tpu32-20261023T1659", FRI_NIGHT, "https://run/2", self.ledger)
        new, rec = prover.record_failure(self.k, Path(self.d.name), "KernelWorkerStatus.ERROR", FRI_NIGHT, path=self.ledger)
        self.assertFalse(new)
        self.assertEqual(rec["status"], "KernelWorkerStatus.ERROR")

    def test_the_cli_reserves_once(self):
        old = sys.argv
        try:
            sys.argv = ["prover.py", "reserve", "--batch", "tpu32-20261023T1659", "--ledger", str(self.ledger)]
            self.assertEqual(prover.main(), 0)
            self.assertEqual(prover.main(), prover.RESERVED_ALREADY)
        finally:
            sys.argv = old


class PrefetchedKernel(unittest.TestCase):
    """2026-10-24: the TPU kernel fetches the pinned weights itself, then vLLM loads that copy offline; a failed child
    fails the kernel (Codex 20261024T194304201890Z, 20261024T194446491583Z)."""

    def built(self, model=prover.PROVER_32B["model"]):
        t = {"target_set": "minif2f/test", "target": "mathd_algebra_478", "order": 1}
        with tempfile.TemporaryDirectory() as d:
            prover.build(d, [(t, 32)], "tpu32-20261024T2000", tpu=True, budget_h=3.0, model=model)
            return (Path(d) / "prover_kernel.py").read_text()

    def test_the_built_kernel_inlines_the_prefetch_and_compiles(self):
        src = self.built()
        compile(src, "prover_kernel_tpu.py", "exec")
        self.assertIn("def prefetch(", src)
        self.assertIn("851bf85d329b0f819e1a44db30e05d16e07d15c0", src)
        self.assertNotIn("HF_PREFETCH_PLACEHOLDER", src)

    def test_vllm_loads_the_verified_local_copy_offline_and_answers_keep_the_model_id(self):
        src = self.built()
        self.assertIn('LLM(model=cfg["model_path"]', src)
        self.assertIn('"HF_HUB_OFFLINE": "1"', src)
        self.assertIn('"config": {"model": cfg["model"]', src)

    def test_a_failed_child_or_download_fails_the_kernel(self):
        src = self.built()
        tail = src[src.rindex('beat("failed", exit=code'):]
        self.assertIn("sys.exit(", tail)
        self.assertIn('beat("failed", reason="download"', src)

    def test_a_smoke_batch_is_named_so_it_never_triggers_the_replacement(self):
        self.assertEqual(prover.tpu_batch_name("tpu32-", True, "20261024T2000"), "smoke-tpu32-20261024T2000")
        self.assertEqual(prover.tpu_batch_name("tpu32-", False, "20261024T2000"), "tpu32-20261024T2000")

    def test_the_real_builder_makes_a_one_problem_smoke_batch(self):
        import relay
        from unittest import mock
        open_list = [{"target_set": "minif2f/test", "target": t, "rung": "imo", "order": i}
                     for i, t in enumerate(["mathd_algebra_478", "mathd_algebra_141"])]
        with tempfile.TemporaryDirectory() as d:
            reach = Path(d) / "reachable.json"
            reach.write_text(json.dumps({"reachable": [{"target_set": "minif2f/test", "target": t["target"]}
                                                       for t in open_list]}))
            out = Path(d) / "k"
            argv = ["prover.py", "next", "--tpu", "--tpu32", "--smoke", "--max-problems", "1", "--out", str(out),
                    "--hours", "3"]
            with mock.patch.object(relay, "fetch_json", return_value={"open": open_list}), \
                    mock.patch.object(prover, "REACHABLE", reach), mock.patch.object(prover, "prover_rows", return_value=[]), \
                    mock.patch.object(prover, "plan_owed", return_value=None), mock.patch.object(sys, "argv", argv):
                self.assertEqual(prover.main(), 0)
            src = (out / "prover_kernel.py").read_text()
            batch = re.search(r'^BATCH = "([^"]+)"', src, re.M).group(1)
            self.assertTrue(batch.startswith("smoke-tpu32-"), batch)
            self.assertEqual(src.count('"target": "mathd_algebra'), 1, "one problem")

    def test_loaded_reports_initialization_only(self):
        src = self.built()
        self.assertIn('load_s=ev["loaded_s"]', src)
        self.assertIn("startup_s=", src)
