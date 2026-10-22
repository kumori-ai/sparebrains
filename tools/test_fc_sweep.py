"""tools/fc_sweep.py: which formal-conjectures declarations are swept, how one `sorry` becomes a candidate, and when
Lean's output counts as a proof. No Lean here: the file shapes are copied from their repo."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import fc_sweep as fc

FILE = """module

public import FormalConjecturesUtil

namespace Hilbert17

@[category textbook, AMS 12]
theorem f_nonneg : ∀ x y : ℝ, 0 ≤ x ^ 2 + y ^ 2 := by
  intro x y
  positivity

@[category textbook, AMS 12]
theorem f_not_sum :
    ¬∃ (n : ℕ), n < 0 := by
  sorry

/-- A test. -/
@[category test, AMS 11]
theorem small : (2 : ℕ) + 2 = 4 := sorry

@[category research open, AMS 11]
theorem hard : ∀ n : ℕ, n = n + 0 := by
  sorry

end Hilbert17
"""


class Scan(unittest.TestCase):
    def test_textbook_and_test_declarations_still_at_sorry_are_the_targets(self):
        self.assertEqual([(d["name"], d["category"]) for d in fc.targets(FILE)],
                         [("f_not_sum", "textbook"), ("small", "test")])

    def test_one_sorry_becomes_the_tactics_and_its_axioms_are_printed_inside_the_namespace(self):
        d = fc.targets(FILE)[0]
        out = fc.candidate(FILE, d, ["omega", "grind"])
        self.assertIn("¬∃ (n : ℕ), n < 0 := by\n  first | (omega) | (grind)\n#print axioms f_not_sum\n", out)
        self.assertIn("theorem small : (2 : ℕ) + 2 = 4 := sorry", out, "only that declaration changes")
        self.assertLess(out.index("#print axioms f_not_sum"), out.index("end Hilbert17"))
        term = fc.candidate(FILE, fc.targets(FILE)[1], ["decide"])
        self.assertIn("theorem small : (2 : ℕ) + 2 = 4 := by\n  first | (decide)\n#print axioms small\n", term)


class Canary(unittest.TestCase):
    def test_the_canary_is_a_target_and_its_candidate_is_well_formed(self):
        text = fc.CANARY.format(claim="(2 : ℕ) + 2 = 4")
        d = fc.targets(text)
        self.assertEqual([x["name"] for x in d], ["sweep_canary"])
        self.assertIn("#print axioms sweep_canary", fc.candidate(text, d[0], ["decide"]))


class RunLean(unittest.TestCase):
    def test_lean_gets_an_absolute_path_because_it_runs_inside_their_checkout(self):
        import tempfile
        from unittest import mock
        import os
        with tempfile.TemporaryDirectory(dir=".") as d, mock.patch.object(fc.subprocess, "run") as run:
            run.return_value = mock.Mock(stdout="", stderr="")
            fc.run_lean(os.path.relpath(d), "x", "t")          # relative, as the workflow passes `fc`
            cmd, kw = run.call_args.args[0], run.call_args.kwargs
            self.assertTrue(Path(cmd[-1]).is_absolute(), cmd)
            self.assertTrue(Path(cmd[-1]).exists())


class Prover(unittest.TestCase):
    def test_only_the_proof_body_is_spliced_under_their_statement(self):
        d = fc.targets(FILE)[0]
        reply = "```lean4\ntheorem f_not_sum : ¬∃ (n : ℕ), n < 0 := by\n  simp\n```"   # a weakened restatement
        out = fc.with_proof(FILE, d, reply)
        self.assertIn("theorem f_not_sum :\n    ¬∃ (n : ℕ), n < 0 := by\n  simp\n#print axioms f_not_sum", out)
        self.assertIsNone(fc.with_proof(FILE, d, "I cannot prove this."))

    def test_the_prompt_carries_the_files_context_and_the_statement(self):
        d = fc.targets(FILE)[1]
        p = fc.prompt(FILE, d)
        self.assertIn("namespace Hilbert17", p)
        self.assertIn("theorem small : (2 : ℕ) + 2 = 4 := sorry", p)
        self.assertNotIn("theorem hard", p, "nothing after the target")

    def test_untrusted_lean_runs_as_the_sandbox_user_with_an_empty_environment(self):
        cmd = fc.lean_cmd("/w/fc/.sweep/x.lean", user="sbjudge", path="/h/.elan/bin:/usr/bin")
        self.assertEqual(cmd[:6], ["sudo", "-n", "-u", "sbjudge", "env", "-i"])
        self.assertIn("PATH=/h/.elan/bin:/usr/bin", cmd)
        self.assertEqual(cmd[-6:], ["lake", "env", "lean", "-M", str(fc.LEAN_MEM_MB), "/w/fc/.sweep/x.lean"])
        self.assertEqual(fc.lean_cmd("/f.lean", user=None, path="p"), ["lake", "env", "lean", "-M", str(fc.LEAN_MEM_MB), "/f.lean"])

    def test_the_judges_lean_processes_fit_the_runner_together(self):
        # fc_prove 39695793555 (2026-10-22): the runner died 3 min into judging 4 at once, so nothing after it ran
        self.assertLessEqual(fc.JUDGE_WORKERS * fc.LEAN_MEM_MB, 12 * 1024, "16 GB runner, room left for the OS")

    def test_each_run_takes_declarations_without_a_prover_row_yet(self):
        work = [("a.lean", "", {"name": "x"}), ("a.lean", "", {"name": "y"}), ("b.lean", "", {"name": "x"})]
        rows = [{"file": "a.lean", "name": "x", "verdict": "open"}]
        self.assertEqual([(w[0], w[2]["name"]) for w in fc.owed(work, rows, 5)], [("a.lean", "y"), ("b.lean", "x")])
        self.assertEqual(len(fc.owed(work, rows, 1)), 1)

    def test_a_check_that_ran_out_of_memory_or_time_says_nothing_about_the_proof(self):
        self.assertTrue(fc.resource_limited("x.lean:1:4: error: (kernel) excessive memory consumption detected"))
        self.assertTrue(fc.resource_limited("timeout"))
        self.assertFalse(fc.resource_limited("x.lean:3:2: error: unsolved goals"))
        work = [("a.lean", "", {"name": "x"}), ("a.lean", "", {"name": "y"})]
        rows = [{"file": "a.lean", "name": "x", "verdict": "resource"}, {"file": "a.lean", "name": "y", "verdict": "reject"}]
        self.assertEqual([w[2]["name"] for w in fc.owed(work, rows, 5)], ["x"], "inconclusive: asked again")
        capped = {"file": "a.lean", "name": "x", "verdict": "no_proof", "finish": "length", "tokens": fc.leanstral_cap()}
        mixed = [capped, {"file": "a.lean", "name": "x", "verdict": "resource", "effort": "none"}]
        self.assertEqual(fc.effort(work[0], mixed), "none", "a resource row neither counts as an answer nor as asked")
        self.assertEqual([w[2]["name"] for w in fc.owed(work[:1], mixed, 5)], ["x"])

    def test_a_declaration_cut_off_at_the_cap_comes_back_first_without_long_reasoning(self):
        work = [("a.lean", "", {"name": "x"}), ("a.lean", "", {"name": "y"}), ("b.lean", "", {"name": "z"})]
        rows = [{"file": "a.lean", "name": "x", "verdict": "no_proof", "finish": "length", "tokens": fc.leanstral_cap()},
                {"file": "a.lean", "name": "y", "verdict": "reject", "finish": "stop"}]
        out = fc.owed(work, rows, 5)
        self.assertEqual([(w[2]["name"], fc.effort(w, rows)) for w in out], [("x", "none"), ("z", None)])
        rows.append({"file": "a.lean", "name": "x", "verdict": "no_proof", "finish": "length",
                     "tokens": fc.leanstral_cap(), "effort": "none"})
        self.assertEqual([w[2]["name"] for w in fc.owed(work, rows, 5)], ["z"], "asked both ways: done")


class Verdict(unittest.TestCase):
    def test_a_proof_needs_no_error_in_the_declaration_and_no_sorryax(self):
        ok = "f.lean:15:2: warning: declaration uses 'sorry'\n'Hilbert17.f_not_sum' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        self.assertTrue(fc.proved(ok, "f_not_sum", (12, 14)))
        err = "f.lean:14:2: error: omega could not prove the goal\n'Hilbert17.f_not_sum' depends on axioms: [sorryAx]\n"
        self.assertFalse(fc.proved(err, "f_not_sum", (12, 14)))
        self.assertFalse(fc.proved("'Hilbert17.f_not_sum' depends on axioms: [propext, sorryAx]\n", "f_not_sum", (12, 14)))
        self.assertFalse(fc.proved("", "f_not_sum", (12, 14)), "no axioms line is never a proof")
        other = "f.lean:30:2: error: unrelated\n'Hilbert17.f_not_sum' does not depend on any axioms\n"
        self.assertTrue(fc.proved(other, "f_not_sum", (12, 14)), "an error elsewhere in the file is not this declaration's")


if __name__ == "__main__":
    unittest.main()
