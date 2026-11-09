"""tools/blueprint.py: a guide's blueprint is a list of propositions and nothing else; the tool writes every line of
proof text, audits each statement in Lean for smuggled proof terms, drops a statement equivalent to the target, and
keeps only a sketch Lean calls wellformed. Codex 20261109T204513251417Z, 204946451069Z, 205417832903Z: the three ways
a guide's proof leaked past the earlier gates are regressions here."""
import sys
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
