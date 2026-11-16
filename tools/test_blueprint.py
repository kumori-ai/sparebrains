"""tools/blueprint.py: a guide's blueprint is a list of propositions and nothing else; the tool writes every line of
proof text, audits each statement in Lean for smuggled proof terms, drops a statement equivalent to the target, and
keeps only a sketch Lean calls wellformed. Codex 20261109T204513251417Z, 204946451069Z, 205417832903Z: the three ways
a guide's proof leaked past the earlier gates are regressions here."""
import hashlib
import json
import sys
import tempfile
import unittest
from unittest.mock import Mock
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import blueprint

PREFIX = ("import Mathlib\n\nopen scoped Nat\n\n/-- doc -/\ntheorem demo (n : ℕ) (h : 0 < n) :\n    n + 0 = n := by")
STMTS = ["n ≠ 0", "n + 0 = n ∨ n = 0"]


class StatementsOnly(unittest.TestCase):
    def test_the_reply_is_read_as_a_json_list_of_statements_and_nothing_else(self):
        reply = ("Here is my plan.\n```json\n[\"n ≠ 0\", \" n + 0 = n ∨ n = 0 \"]\n```\n"
                 "by_cases bad : False\n· exact False.elim bad\n· rfl\n")
        self.assertEqual(blueprint.statements(reply), STMTS)
        self.assertEqual(blueprint.statements("no list here"), [])
        self.assertEqual(blueprint.statements('[1, "x"]'), ["x"], "only strings are statements")

    def test_the_sketch_holds_no_guide_text_beyond_the_statements(self):
        glue = "by_cases bad : False"
        sk = blueprint.sketch(PREFIX, STMTS + [glue])
        self.assertTrue(sk.startswith(PREFIX))
        body = sk[len(PREFIX):]
        for line in body.strip("\n").split("\n"):
            self.assertTrue(blueprint.HAVE.match(line) or line.strip() == "sorry" or line.strip() == blueprint.FINAL,
                            f"a line the tool did not write: {line!r}")
        self.assertIn(f"  have bp_1 : {STMTS[0]} := by\n    sorry\n", body)
        self.assertIn(f"  have bp_3 : {glue} := by", body, "guide text survives only as a statement to prove")
        self.assertNotIn("False.elim", body, "the dead-branch glue of Codex 20261109T204946451069Z is not in the sketch")
        self.assertNotIn("rfl", body)
        self.assertTrue(body.rstrip().endswith(blueprint.FINAL))

    def test_the_audit_file_defines_the_check_after_the_imports_and_runs_each_statement_in_its_own_example(self):
        text, lines = blueprint.audit_text(PREFIX, STMTS)
        self.assertLess(text.index("import Mathlib"), text.index('elab "audit_prop "'))
        self.assertNotIn("theorem", text, "the target's statement is not in the file, only its binders")
        self.assertEqual(len(lines), 2)
        for i, s in enumerate(STMTS):
            self.assertEqual(text.split("\n")[lines[i] - 1].strip(), f"audit_prop ({s})")
            self.assertTrue(text.split("\n")[lines[i] - 2].startswith("example (n : ℕ) (h : 0 < n)"), "one example a statement")
        # a later statement may name an earlier lemma: bp_1 is a hypothesis of statement 2's example
        self.assertIn(f"example (n : ℕ) (h : 0 < n) (bp_1 : {STMTS[0]}) : True := by\n  audit_prop ({STMTS[1]})", text)
        self.assertNotIn(f"(bp_1 : {STMTS[0]}) : True := by\n  audit_prop ({STMTS[0]})", text)

    def test_split_signature_gives_the_binders_and_the_conclusion(self):
        b, c = blueprint.split_signature(PREFIX)
        self.assertEqual(b, "(n : ℕ) (h : 0 < n)")
        self.assertEqual(c, "n + 0 = n")
        b, c = blueprint.split_signature("theorem t (f : ℕ → ℕ) (h : ∀ x, f x = x) : f 2 = 2 := by")
        self.assertEqual((b, c), ("(f : ℕ → ℕ) (h : ∀ x, f x = x)", "f 2 = 2"))


class Gate(unittest.TestCase):
    """Lean is faked by output text; the real audit's behavior on these inputs is recorded in DECISIONS 2026-11-09."""
    def lean(self, audit_out="", dup_out=""):
        calls = []

        def run_lean(text, timeout=180):
            calls.append(text)
            return (audit_out if 'elab "audit_prop "' in text else dup_out), 1.0
        return run_lean, calls

    def test_too_few_or_too_many_statements_never_reach_lean(self):
        run_lean, calls = self.lean()
        judge = Mock()
        for stmts in ([], ["a"], [f"s{i}" for i in range(7)]):
            g = blueprint.gate(PREFIX, stmts, run_lean, judge)
            self.assertFalse(g["ok"])
            self.assertIn("statements", g["why"][0])
        self.assertEqual(calls, [])
        judge.assert_not_called()

    def test_a_closer_that_times_out_does_not_hide_one_that_works_and_the_blueprint_records_it(self):
        """2026-11-16: hole 1's six sub-statements close it by `grind` in 13 s, but `aesop` ran out of heartbeats
        first, and `first | ...` does not catch that: the one closing line failed and the gate said REJECT."""
        stmts = ["n ≠ 0", "0 < n"]
        starts = dict(blueprint.duplicate_text(PREFIX, stmts)[1])
        not_dup = "".join(f"proof.lean:{starts[r] + 1}:2: error: linarith failed\n" for r in ("r1", "r2"))
        run_lean, _ = self.lean(audit_out="AUDIT_OK\nAUDIT_OK\n", dup_out=not_dup)

        def judge(text):
            if text.rstrip().endswith("\n  grind"):
                return {"verdict": "wellformed", "reason": ""}
            return {"verdict": "reject", "reason": "(deterministic) timeout at `whnf`, maximum number of heartbeats"}
        g = blueprint.gate(PREFIX, stmts, run_lean, judge)
        self.assertTrue(g["ok"], g["why"])
        self.assertEqual(g["final"], "grind")
        self.assertTrue(g["sketch"].endswith("    sorry\n  grind\n"))
        self.assertEqual(blueprint.sketch(PREFIX, stmts, g["final"]), g["sketch"])
        none = blueprint.gate(PREFIX, stmts, run_lean, lambda text: {"verdict": "reject", "reason": "unsolved goals"})
        self.assertFalse(none["ok"])
        self.assertNotIn("final", none)

    def test_a_proof_term_inside_a_statement_fails_the_audit_by_index(self):
        stmts = ["n ≠ 0", "(Nat.add_zero n : n + 0 = n) = Nat.add_zero n", "0 < n"]
        _, lines = blueprint.audit_text(PREFIX, stmts)
        out = (f"proof.lean:{lines[1]}:2: error: AUDIT_FAIL proof term in statement: Nat.add_zero n\n"
               "AUDIT_OK\nAUDIT_OK\n")
        run_lean, _ = self.lean(audit_out=out)
        a = blueprint.audit(PREFIX, stmts, run_lean)
        self.assertEqual([x["ok"] for x in a], [True, False, True])
        self.assertIn("proof term", a[1]["why"])
        g = blueprint.gate(PREFIX, stmts, run_lean, Mock())
        self.assertFalse(g["ok"])
        self.assertIn("statement 2", g["why"][0])

    def test_a_statement_lean_cannot_read_fails_the_audit_with_leans_words(self):
        stmts = ["n ≠ 0", "foo n = 1"]
        _, lines = blueprint.audit_text(PREFIX, stmts)
        out = f"proof.lean:{lines[1]}:19: error: unknown identifier 'foo'\nAUDIT_OK\n"
        run_lean, _ = self.lean(audit_out=out)
        a = blueprint.audit(PREFIX, stmts, run_lean)
        self.assertEqual([x["ok"] for x in a], [True, False])
        self.assertIn("unknown identifier", a[1]["why"])

    def test_an_audit_with_fewer_oks_than_statements_and_no_error_is_not_a_pass(self):
        run_lean, _ = self.lean(audit_out="AUDIT_OK\n")           # one of two reported; Lean said nothing of the other
        a = blueprint.audit(PREFIX, STMTS, run_lean)
        self.assertFalse(all(x["ok"] for x in a))

    def test_a_statement_automation_proves_equivalent_to_the_target_is_dropped(self):
        stmts = ["n = n + 0", "n ≠ 0"]
        text, starts = blueprint.duplicate_text(PREFIX, stmts)
        self.assertIn("(bp_dup : n = n + 0) : n + 0 = n := by", text)
        self.assertIn("(bp_tgt : n + 0 = n) : n = n + 0 := by", text)
        # statement 1: both directions pass (no error in its two examples); statement 2: the reverse fails
        rev2 = dict(starts)["r2"]
        out = f"proof.lean:{rev2 + 1}:2: error: linarith failed\n"
        run_lean, _ = self.lean(audit_out="AUDIT_OK\nAUDIT_OK\n", dup_out=out)
        self.assertEqual(blueprint.duplicates(PREFIX, stmts, run_lean), {0})
        g = blueprint.gate(PREFIX, stmts, run_lean, Mock(return_value={"verdict": "wellformed"}))
        self.assertFalse(g["ok"])
        self.assertIn("statement 1", g["why"][0])
        self.assertIn("equivalent", g["why"][0])

    def test_a_timeout_in_the_duplicate_run_drops_nothing_and_is_said(self):
        run_lean, _ = self.lean(dup_out="timeout after 180s")
        self.assertEqual(blueprint.duplicates(PREFIX, STMTS, run_lean), set())
        run_lean, _ = self.lean(dup_out="killed (exit -9) under the 4000 MB memory limit")                       # kumori #683: a killed run is not a silent one
        self.assertEqual(blueprint.duplicates(PREFIX, STMTS, run_lean), set())

    def test_a_silent_duplicate_run_means_every_example_passed_and_every_statement_is_a_duplicate(self):
        run_lean, _ = self.lean(dup_out="")
        self.assertEqual(blueprint.duplicates(PREFIX, STMTS, run_lean), {0, 1})

    def test_the_sketch_must_be_wellformed_a_full_proof_or_a_broken_assembly_is_rejected(self):
        _, starts = blueprint.duplicate_text(PREFIX, STMTS)
        s = dict(starts)
        dup = "".join(f"proof.lean:{s[f'r{i}'] + 1}:2: error: linarith failed\n" for i in (1, 2))   # no statement equivalent
        run_lean, _ = self.lean(audit_out="AUDIT_OK\nAUDIT_OK\n", dup_out=dup)
        g = blueprint.gate(PREFIX, STMTS, run_lean, Mock(return_value={"verdict": "wellformed", "reason": ""}))
        self.assertTrue(g["ok"])
        self.assertEqual(g["sketch"], blueprint.sketch(PREFIX, STMTS))
        g = blueprint.gate(PREFIX, STMTS, run_lean, Mock(return_value={"verdict": "accept", "reason": "kernel accepted"}))
        self.assertFalse(g["ok"], "no hole left to prove: the statements alone closed it, nothing for a small lane")
        g = blueprint.gate(PREFIX, STMTS, run_lean, Mock(return_value={"verdict": "reject", "reason": "lean exit 1: unsolved goals"}))
        self.assertFalse(g["ok"])
        self.assertIn("do not imply the target", g["why"][0])


class Fill(unittest.TestCase):
    """The fill step: each hole as its own lemma with the earlier statements as hypotheses (the queue's extract_goal
    clears them: on 2026-11-09 hole 5 of the first blueprint lost bp_1..bp_4, the very steps that prove it), Lean's
    closers first, then each ask in turn; every hole is attempted, so failed and unattempted stay apart (Codex f6)."""
    S3 = ["n ≠ 0", "0 < n → n ≠ 0", "n + 0 = n"]

    def test_a_holes_lemma_carries_the_binders_and_the_earlier_statements(self):
        self.assertEqual(blueprint.lemma_text(PREFIX, self.S3, 0), "theorem sb_goal (n : ℕ) (h : 0 < n) : n ≠ 0 := by")
        self.assertEqual(blueprint.lemma_text(PREFIX, self.S3, 2),
                         "theorem sb_goal (n : ℕ) (h : 0 < n) (bp_1 : n ≠ 0) (bp_2 : 0 < n → n ≠ 0) : n + 0 = n := by")

    def test_the_lean_tier_runs_the_baselines_recipes_apart_and_the_found_closer_is_spliced(self):
        calls = []

        def run_lean(text, timeout=180):
            calls.append(text)
            return "", 1.0                                    # every recipe passes the batch: judged one by one below
        judge = lambda text: {"verdict": "accept" if text.rstrip().endswith("\n  grind") else "reject", "reason": "", "output": ""}
        self.assertEqual(blueprint.lean_tier("theorem sb_goal : True := by", judge, run_lean), "grind")
        self.assertTrue(calls and "sb_goal_r0" in calls[0], "replay.baseline_one's batch, one theorem per recipe")
        f = blueprint.fill(PREFIX, self.S3, judge, asks=[], closer=lambda lp: "grind" if lp.endswith(": 0 < n → n ≠ 0 := by") else None)
        self.assertEqual((f["closed_by"], f["failed"]), ({2: "lean"}, [1, 3]))

    def judge(self, lean_closes=(), accept_final=True):
        def judge_text(text):
            if blueprint.FINAL in text and "sb_goal" in text:
                return {"verdict": "accept" if any(f": {s} := by" in text for s in lean_closes) else "reject", "output": "err"}
            if "sb_goal" in text:                                       # a lane's lemma proof: accepted when it says so
                return {"verdict": "accept" if "exact good" in text else "reject", "output": "bad", "reason": "bad"}
            return {"verdict": "accept" if accept_final else "reject", "output": ""}
        return judge_text

    def test_lean_then_the_asks_in_turn_and_the_proved_bodies_are_spliced_under_their_have(self):
        weak = Mock(return_value="```lean\n  exact bad\n```")
        strong = Mock(side_effect=["```lean\n  exact good\n```", "```lean\n  exact good\n```"])
        f = blueprint.fill(PREFIX, self.S3, self.judge(lean_closes=[self.S3[0]]), asks=[weak, strong])
        self.assertEqual(f["closed_by"], {1: "lean", 2: 1, 3: 1})
        self.assertEqual((f["failed"], f["unattempted"]), ([], []))
        self.assertEqual(weak.call_count, 1, "rotation: hole 2 goes to the strong lane first; hole 3 to the weak one, then the strong")
        self.assertEqual(f["final"], "accept")
        body = f["accepted"][len(PREFIX):]
        self.assertIn(f"  have bp_1 : {self.S3[0]} := by\n    {blueprint.FINAL}\n", body)
        self.assertIn(f"  have bp_2 : {self.S3[1]} := by\n    exact good\n", body)
        self.assertNotIn("sorry", body)
        self.assertNotIn("exact bad", body)
        self.assertEqual([(t["hole"], t["by"], t["verdict"]) for t in f["tries"]],
                         [(2, 1, "accept"), (3, 0, "reject"), (3, 1, "accept")])

    def test_a_hole_nobody_proves_is_failed_and_the_later_holes_are_still_attempted(self):
        weak = Mock(return_value="```lean\n  exact bad\n```")
        f = blueprint.fill(PREFIX, self.S3, self.judge(lean_closes=[self.S3[2]]), asks=[weak])
        self.assertEqual((f["failed"], f["unattempted"], f["closed_by"]), ([1, 2], [], {3: "lean"}))
        self.assertEqual(weak.call_count, 6, "pass 1 one try each, pass 2 two tries each, on the two open holes")
        self.assertNotIn("final", f)

    def test_holes_the_ask_budget_never_reached_are_unattempted_not_failed(self):
        weak = Mock(return_value="```lean\n  exact bad\n```")
        f = blueprint.fill(PREFIX, self.S3, self.judge(), asks=[weak], max_asks=2)
        self.assertEqual((f["failed"], f["unattempted"]), ([1, 2], [3]), "breadth first: one try each before any second")
        self.assertEqual((f["asked"], f["answered"], f["unanswered"]), (2, 2, 0))

    def test_every_open_hole_gets_one_try_before_any_gets_its_second(self):
        weak = Mock(return_value="```lean\n  exact bad\n```")
        f = blueprint.fill(PREFIX, self.S3, self.judge(), asks=[weak], max_asks=9)
        order = [t["hole"] for t in f["tries"]]
        self.assertEqual(order, [1, 2, 3, 1, 1, 2, 2, 3, 3], "run 42705124685: holes 1-3 ate the budget, 4-6 never asked")
        self.assertEqual((f["failed"], f["unattempted"], f["asked"]), ([1, 2, 3], [], 9))

    def test_six_holes_three_lanes_twelve_asks_reach_every_hole_before_any_second_ask_rotating_lanes(self):
        """Codex 20261109T220030181138Z f1: hole by hole, lane by lane spent three asks on hole 1 before hole 2 was
        reached; with the manifest's budget holes 5 and 6 were never asked."""
        six = [f"n + {k} = {k} + n" for k in range(6)]
        lanes = [Mock(return_value="```lean\n  exact bad\n```") for _ in range(3)]
        f = blueprint.fill(PREFIX, six, self.judge(), asks=lanes, max_asks=12)
        self.assertEqual([t["hole"] for t in f["tries"]], [1, 2, 3, 4, 5, 6, 1, 2, 3, 4, 5, 6])
        self.assertEqual([t["by"] for t in f["tries"]], [0, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 0], "lanes rotate across holes")
        self.assertEqual((f["failed"], f["unattempted"], f["asked"]), ([1, 2, 3, 4, 5, 6], [], 12))
        self.assertEqual([m.call_count for m in lanes], [4, 4, 4])

    def test_a_rejected_hole_proof_goes_through_the_repair_hook_before_it_counts_as_failed(self):
        weak = Mock(return_value="```lean\n  exact bad\n```")
        repair = Mock(side_effect=lambda body, pre, said: "  exact good\n" if pre.endswith(": 0 < n → n ≠ 0 := by") else None)
        f = blueprint.fill(PREFIX, self.S3, self.judge(), asks=[weak], repair=repair)
        self.assertEqual(f["closed_by"], {2: 0})
        self.assertEqual([t["repaired"] for t in f["tries"] if t["hole"] == 2], [True])
        self.assertEqual(f["failed"], [1, 3])
        self.assertEqual(repair.call_args_list[0].args[0], "  exact bad\n")

    def test_a_lane_that_never_answers_spends_budget_and_is_counted_as_unanswered_not_as_tries(self):
        silent = Mock(return_value=None)                   # parked, capped or erroring: make_ask returns None
        f = blueprint.fill(PREFIX, self.S3, self.judge(), asks=[silent], max_asks=12)
        self.assertEqual((f["failed"], f["unattempted"], f["tries"]), ([], [1, 2, 3], []))
        self.assertEqual((f["asked"], f["answered"], f["unanswered"]), (6, 0, 6), "Codex f3: budget spent, nothing answered")


class KaggleBatch(unittest.TestCase):
    """The holes of a gated blueprint as a prover batch and back (DECISIONS.md 2026-11-15): Goedel-Prover on Kaggle is
    a batch, not a router lane, so attempt.py --pilot cannot reach it (Codex 20261115T234113711421Z f3)."""
    S3 = Fill.S3
    TARGET = PREFIX + "\n  sorry\n"

    def work(self, tmp, ok=True):
        bp = Path(tmp) / "demo-20261109T000000Z.json"
        bp.write_text(json.dumps({"ok": ok, "statements": self.S3}))
        man = {"id": "pilot-x", "problems": ["minif2f/test/demo"]}
        return bp, blueprint.kaggle_work(man, 8, read=lambda s, t: self.TARGET, find=lambda name: bp if ok else None,
                                         rel=lambda path: path.name)

    def test_every_hole_is_exported_as_its_own_file_with_the_earlier_statements_as_hypotheses(self):
        with tempfile.TemporaryDirectory() as tmp:
            bp, work = self.work(tmp)
        self.assertEqual([(w["target_set"], w["target"], w["n"], w["guided"]["hole"]) for w in work],
                         [("minif2f/test", "demo", 8, k) for k in (1, 2, 3)])
        self.assertTrue(work[2]["statement"].startswith("import Mathlib\n\nopen scoped Nat\n\n"))
        self.assertTrue(work[2]["statement"].endswith(
            "theorem sb_goal (n : ℕ) (h : 0 < n) (bp_1 : n ≠ 0) (bp_2 : 0 < n → n ≠ 0) : n + 0 = n := by\n  sorry\n"),
            "2026-11-09: the queue's extract_goal dropped bp_1..bp_4 from hole 5")
        g = work[0]["guided"]
        self.assertEqual((g["manifest"], g["holes"], g["n"], g["blueprint"]), ("pilot-x", 3, 8, "demo-20261109T000000Z.json"))
        self.assertEqual(len(g["blueprint_sha"]), 64)
        self.assertEqual(len(g["target_sha"]), 64)
        self.assertNotIn("goal", work[0], "a `goal` field would send the answers down the public goal-closer path")
        self.assertNotIn("arm", work[0])

    def test_an_export_that_is_not_what_the_manifest_froze_is_refused(self):
        """Codex 20261116T001213948778Z f4: the manifest's hashes were documentary; a newer blueprint or an edited
        target before the push would have changed the experiment silently."""
        with tempfile.TemporaryDirectory() as tmp:
            bp, work = self.work(tmp)
            g = work[0]["guided"]
            read, pick, rel = (lambda s, t: self.TARGET), (lambda name: bp), (lambda path: path.name)
            frozen = {"id": "pilot-x", "problems": ["minif2f/test/demo"], "blueprint": {"sha256": g["blueprint_sha"]},
                      "target_sha256": {"minif2f/test/demo": g["target_sha"]}}
            self.assertEqual(len(blueprint.kaggle_work(frozen, 8, read=read, find=pick, rel=rel)), 3)
            with self.assertRaises(SystemExit):
                blueprint.kaggle_work({**frozen, "blueprint": {"sha256": "0" * 64}}, 8, read=read, find=pick, rel=rel)
            with self.assertRaises(SystemExit):
                blueprint.kaggle_work(frozen, 8, read=lambda s, t: self.TARGET + "\n", find=pick, rel=rel)

    def test_a_problem_with_no_gated_blueprint_exports_nothing(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(self.work(tmp, ok=False)[1], [])

    def judge(self, lean_closes=(), accept_final=True):
        return Fill.judge(self, lean_closes, accept_final)

    GOOD = "```lean4\ntheorem sb_goal (n : ℕ) : n = n := by\n  exact good\n```"
    BAD = "```lean4\ntheorem sb_goal (n : ℕ) : n = n := by\n  exact bad\n```"
    proof_of = staticmethod(lambda text: ("  exact good\n" if "exact good" in text else "  exact bad\n") if "sb_goal" in text else None)

    def fill(self, samples, **kw):
        kw.setdefault("judge_text", self.judge())
        return blueprint.fill_samples(PREFIX, self.S3, samples, kw.pop("judge_text"), proof_of=self.proof_of, planned=2, **kw)

    def test_lean_first_then_each_sample_in_order_and_the_first_accept_closes_only_its_hole(self):
        f = self.fill({1: [self.BAD, self.BAD], 2: [self.BAD, self.GOOD], 3: [self.GOOD, self.GOOD]},
                      judge_text=self.judge(lean_closes=[self.S3[0]]))
        self.assertEqual(f["closed_by"], {1: "lean", 2: "sample", 3: "sample"})
        self.assertEqual([(t["hole"], t["sample"], t["verdict"]) for t in f["tries"]], [(2, 0, "reject"), (2, 1, "accept"), (3, 0, "accept")])
        self.assertEqual((f["asked"], f["answered"], f["no_proof"], f["unread"]), (6, 3, 0, 3),
                         "asked is every sample generated: the two Lean made unneeded and the one after an accept are cost too")
        self.assertEqual((f["final"], f["truncated"]), ("accept", False))
        self.assertIn(f"  have bp_2 : {self.S3[1]} := by\n    exact good\n", f["accepted"])
        self.assertNotIn("sorry", f["accepted"])

    def test_one_proved_hole_is_not_a_solve_and_the_whole_proof_is_not_checked(self):
        f = self.fill({1: [self.BAD, self.BAD], 2: [self.GOOD, self.BAD], 3: [self.BAD, "no fenced proof at all"]})
        self.assertEqual((f["closed_by"], f["failed"], f["unattempted"]), ({2: "sample"}, [1, 3], []))
        self.assertNotIn("final", f, "null means not checked, never a kernel reject (Codex 20261115T234449896697Z)")
        self.assertNotIn("accepted", f)
        self.assertEqual((f["answered"], f["no_proof"]), (4, 1))

    def test_a_batch_the_gpu_budget_cut_short_is_truncated_and_its_empty_holes_are_unattempted(self):
        """Codex 20261115T235234646209Z f2: the kernel's fit_chunk gave hole 1 eight samples and hole 2 one of eight."""
        f = self.fill({1: [self.BAD, self.BAD], 2: [self.BAD]})
        self.assertEqual((f["failed"], f["unattempted"]), ([1, 2], [3]))
        self.assertEqual((f["planned"], f["generated"]), ({1: 2, 2: 2, 3: 2}, {1: 2, 2: 1, 3: 0}))
        self.assertTrue(f["truncated"], "an incomplete read, not an exhausted one")

    def test_a_sample_the_judge_did_not_finish_is_not_a_failed_hole(self):
        """Codex 20261116T000117894936Z f3: check.py returns a reject for a timeout or a memory kill; read as a failed
        hole, an unfinished judge run would pass for a finished feasibility result."""
        slow = lambda text: {"verdict": "reject", "reason": "timeout after 300s" if ": n ≠ 0 := by" in text else "bad", "output": ""}
        f = self.fill({1: [self.BAD, self.BAD], 2: [self.BAD, self.BAD], 3: [self.BAD, self.BAD]}, judge_text=slow)
        self.assertEqual((f["judge_unfinished"], f["failed"]), ([1], [2, 3]))
        self.assertFalse(f["judging_complete"])
        killed = lambda text: {"verdict": "reject", "reason": "killed (exit 137) under the 4000 MB memory limit", "output": ""}
        self.assertEqual(self.fill({1: [self.BAD], 2: [self.BAD], 3: [self.BAD]}, judge_text=killed)["judge_unfinished"], [1, 2, 3])
        self.assertTrue(self.fill({1: [self.BAD, self.BAD], 2: [self.BAD, self.BAD], 3: [self.BAD, self.BAD]})["judging_complete"])

    def test_the_whole_proofs_verdict_keeps_its_reason_and_a_timeout_there_is_unfinished_too(self):
        def judge_text(text):
            if "sb_goal" in text:
                return {"verdict": "accept", "reason": "", "output": ""}
            return {"verdict": "reject", "reason": "timeout after 300s", "output": ""}
        f = self.fill({1: [self.GOOD, self.GOOD], 2: [self.GOOD, self.GOOD], 3: [self.GOOD, self.GOOD]}, judge_text=judge_text)
        self.assertEqual((f["final"], f["final_reason"], f["judging_complete"]), ("reject", "timeout after 300s", False))
        self.assertNotIn("accepted", f)

    def test_a_rejected_sample_goes_through_the_free_chain_and_is_marked_repaired(self):
        repair = Mock(side_effect=lambda body, pre, said: "  exact good\n" if pre.endswith(": 0 < n → n ≠ 0 := by") else None)
        f = self.fill({1: [self.BAD], 2: [self.BAD], 3: [self.BAD]}, repair=repair)
        self.assertEqual(f["closed_by"], {2: "sample"})
        self.assertEqual([(t["hole"], t["repaired"]) for t in f["tries"]], [(1, False), (2, True), (3, False)])

    def test_a_holes_own_lemma_splits_at_the_signatures_colon_not_one_inside_its_conclusion(self):
        """2026-11-16: hole 1's lemma concludes `∀ m : ℕ, ...`; split at the LAST top-level colon, its binders took
        `: ∀ m` with them and the gate rejected all six sub-statements on a parse error."""
        lemma = "import Mathlib\n\ntheorem sb_goal (S : Finset ℕ) (h : 0 < 1) : ∀ m : ℕ, m ∈ S → (m : ℤ) = m := by"
        self.assertEqual(blueprint.split_signature(lemma), ("(S : Finset ℕ) (h : 0 < 1)", "∀ m : ℕ, m ∈ S → (m : ℤ) = m"))
        self.assertEqual(blueprint.split_signature(PREFIX), ("(n : ℕ) (h : 0 < n)", "n + 0 = n"))

    def test_a_continuing_manifest_exports_only_its_open_holes_and_says_which(self):
        """2026-11-16: the second batch samples holes 1 and 3; the closed ones are carried, not sampled again."""
        with tempfile.TemporaryDirectory() as tmp:
            bp, _ = self.work(tmp)
            man = {"id": "pilot-x", "problems": ["minif2f/test/demo"], "holes": [1, 3]}
            work = blueprint.kaggle_work(man, 8, read=lambda s, t: self.TARGET, find=lambda name: bp, rel=lambda path: path.name)
        self.assertEqual([(w["guided"]["hole"], w["guided"]["exported"], w["guided"]["holes"]) for w in work],
                         [(1, [1, 3], 3), (3, [1, 3], 3)])

    def test_a_holes_own_blueprint_is_exported_as_its_holes_and_refused_unless_it_is_the_frozen_gated_one(self):
        """2026-11-16: hole 1 is a theorem in itself; the guide split it and its pieces go to the prover instead of
        more samples of the whole (Codex 20261116T051804114308Z q2)."""
        with tempfile.TemporaryDirectory() as tmp:
            bp, first = self.work(tmp)
            sp = Path(tmp) / "demo.bp1-x.json"
            doc = {"ok": True, "statements": ["n = n", "0 ≤ n"], "parent_sha": first[0]["guided"]["blueprint_sha"], "hole": 1}
            sp.write_text(json.dumps(doc))
            sub = {"hole": 1, "blueprint": sp.name, "sha256": hashlib.sha256(sp.read_bytes()).hexdigest()}
            man = {"id": "pilot-x", "problems": ["minif2f/test/demo"], "holes": [3], "sub": {"minif2f/test/demo": sub}}
            go = lambda m: blueprint.kaggle_work(m, 8, read=lambda s, t: self.TARGET, find=lambda name: bp,
                                                 rel=lambda path: path.name, at=lambda r: Path(tmp) / r)
            work = go(man)
            self.assertEqual([(w["guided"].get("sub"), w["guided"]["hole"], w["guided"]["holes"], w["guided"]["exported"])
                              for w in work], [(None, 3, 3, [3]), (1, 1, 2, [3]), (1, 2, 2, [3])])
            self.assertTrue(work[2]["statement"].endswith("theorem sb_goal (n : ℕ) (h : 0 < n) (bp_1 : n = n) : 0 ≤ n := by\n  sorry\n"),
                            work[2]["statement"][-90:])
            self.assertEqual(work[1]["guided"]["sub_blueprint_sha"], sub["sha256"])
            for bad in ({**man, "holes": [1, 3]}, {k: v for k, v in man.items() if k != "holes"},
                        {**man, "sub": {"minif2f/test/demo": {**sub, "sha256": "0" * 64}}},
                        {**man, "sub": {"minif2f/test/demo": {**sub, "hole": 2}}}):
                with self.assertRaises(SystemExit):
                    go(bad)
            sp.write_text(json.dumps({**doc, "parent_sha": "0" * 64}))
            with self.assertRaises(SystemExit):
                go({**man, "sub": {"minif2f/test/demo": {**sub, "sha256": hashlib.sha256(sp.read_bytes()).hexdigest()}}})

    def test_a_carried_hole_is_judged_again_and_closes_without_a_sample(self):
        """The first batch's closed holes 2 and 4 lived only in Kaggle's output (2026-11-16). A carried body is a
        claim like any sample: Lean judges it on the hole's own lemma before it counts."""
        seen = []
        base = self.judge()
        judge_text = lambda text: (seen.append(text), base(text))[1]
        f = self.fill({1: [self.GOOD, self.GOOD], 3: [self.GOOD, self.BAD]}, judge_text=judge_text,
                      carried={2: ["exact good"]}, exported=[1, 3])
        self.assertEqual(f["closed_by"], {1: "sample", 2: "carried", 3: "sample"})
        self.assertTrue(any(": 0 < n → n ≠ 0 := by\n  exact good\n" in t for t in seen), "the carried body went to the judge")
        self.assertEqual((f["planned"], f["generated"], f["truncated"]), ({1: 2, 2: 0, 3: 2}, {1: 2, 2: 0, 3: 2}, False))
        self.assertEqual(f["final"], "accept")
        self.assertEqual(f["bodies"], {1: {"lines": ["exact good"], "sample": 0, "repaired": False}, 2: {"lines": ["exact good"]},
                                       3: {"lines": ["exact good"], "sample": 0, "repaired": False}})

    def test_a_blueprints_own_closing_line_is_the_one_assembled(self):
        f = self.fill({1: [self.GOOD, self.GOOD], 2: [self.GOOD, self.GOOD], 3: [self.GOOD, self.GOOD]}, final="grind")
        self.assertTrue(f["accepted"].endswith("\n  grind\n"), f["accepted"][-80:])

    def test_a_carried_body_that_no_longer_judges_leaves_its_hole_open_and_is_never_repaired(self):
        repair = Mock(return_value="  exact good\n")
        f = self.fill({1: [self.GOOD, self.GOOD], 3: [self.GOOD, self.GOOD]}, carried={2: ["exact bad"]}, exported=[1, 3])
        self.assertEqual((f["closed_by"], f["carry_failed"], f["unattempted"]), ({1: "sample", 3: "sample"}, [2], [2]))
        self.assertNotIn("final", f, "an open hole: the whole proof is not checked")
        g = blueprint.fill_samples(PREFIX, self.S3, {}, self.judge(), proof_of=self.proof_of, planned=2, repair=repair,
                                   carried={2: ["exact bad"]}, exported=[1, 3])
        self.assertEqual(g["carry_failed"], [2])
        repair.assert_not_called()


@unittest.skipUnless((Path(__file__).parent.parent / ".lake" / "packages" / "mathlib").is_dir(), "needs the local Mathlib build")
class AuditInLean(unittest.TestCase):
    """The audit as Lean runs it (about 20 s): Codex's three proof-carrying propositions fail by name, ordinary
    statements and a bare hypothesis pass. The unit tests above fake Lean; this is the one that can go red for real."""
    def test_proof_terms_fail_hypotheses_and_plain_propositions_pass(self):
        import lean_tools
        prefix = "import Mathlib\n\ntheorem demo (P Q : Prop) (hp : P) (hq : Q) (n : ℕ) (h : 0 < n) : n + 0 = n := by"
        stmts = ["n ≠ 0", "∀ y : ℝ, 0 < y → y ^ 2 > 0", "hp = hp",
                 "(show P → P from id) = id", "(And.intro hp hq : P ∧ Q) = And.intro hp hq",
                 "(Nat.add_zero n : n + 0 = n) = Nat.add_zero n"]
        a = blueprint.audit(prefix, stmts, lean_tools.run_lean)
        self.assertEqual([x["ok"] for x in a], [True, True, True, False, False, False], a)
        for x in a[3:]:
            self.assertIn("proof term in statement", x["why"])


if __name__ == "__main__":
    unittest.main()
