"""The fixer repairs form and only form (issue #3). No Lean here: the kernel judges in Actions."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import fixer

LEAN3 = """  begin
    intro h,
    cases h with x hx,
    have := nat.succ_le_iff.mpr hx,
    exact λ y, y,
    assume k,
    norm_num,
  end
"""


class Lean3Tests(unittest.TestCase):
    def test_a_lean3_block_becomes_lean4(self):
        got = fixer.lean3_to_4(LEAN3)
        self.assertNotIn("begin", got)
        self.assertNotIn("end\n", got)
        self.assertIn("    intro h\n", got)
        self.assertIn("    obtain ⟨x, hx⟩ := h\n", got)
        self.assertIn("Nat.succ_le_iff.mpr hx", got)
        self.assertIn("exact fun y => y", got)
        self.assertIn("    intro k\n", got)
        self.assertFalse(any(l.rstrip().endswith(",") for l in got.splitlines()))

    def test_a_lean4_list_split_over_lines_keeps_its_commas(self):
        p = "  simp only [Finset.sum_range_succ,\n    Nat.succ_eq_add_one]\n  ring\n"
        self.assertEqual(fixer.fix(p), (p, []))

    def test_lean4_with_a_stray_ellipsis_is_not_rewritten(self):
        p = "  have h : x = 1 := ...\n  simp [h]\n"
        self.assertEqual(fixer.fix(p), (p, []))

    def test_lean4_is_left_alone(self):
        p = "  intro h\n  exact ⟨1, by norm_num⟩\n"
        self.assertEqual(fixer.fix(p), (p, []))


class NameTests(unittest.TestCase):
    INDEX = {"Nat.Prime.dvd_of_dvd_pow", "Nat.Prime.two_le", "Real.rpow_natCast", "Nat.succ_le_iff", "Nat.pos_of_ne_zero"}

    def test_same_final_name_in_another_namespace_wins(self):
        self.assertEqual(fixer.closest_name("Prime.two_le", self.INDEX), "Nat.Prime.two_le")

    def test_close_spelling_in_the_same_namespace(self):
        self.assertEqual(fixer.closest_name("Real.rpow_nat_cast", self.INDEX), "Real.rpow_natCast")

    def test_nothing_close_means_no_swap(self):
        self.assertIsNone(fixer.closest_name("Nat.totally_made_up_lemma", self.INDEX))

    def test_fix_swaps_only_names_lean_called_unknown(self):
        proof = "  rw [Real.rpow_nat_cast]\n  exact Nat.Prime.two_le hp\n"
        lean = "x.lean:7:6: error(lean.unknownConstant): Unknown constant `Real.rpow_nat_cast`"
        got, applied = fixer.fix(proof, lean, self.INDEX)
        self.assertEqual(applied, ["names"])
        self.assertIn("rw [Real.rpow_natCast]", got)
        self.assertIn("Nat.Prime.two_le hp", got)                      # not reported unknown: untouched

    def test_without_an_index_names_are_never_guessed(self):
        proof = "  rw [Real.rpow_nat_cast]\n"
        self.assertEqual(fixer.fix(proof, "Unknown constant `Real.rpow_nat_cast`", None), (proof, []))

    def test_the_index_reads_declarations_with_their_namespace(self):
        import tempfile
        d = Path(tempfile.mkdtemp())
        (d / "A.lean").write_text("namespace Nat\n\ntheorem succ_le_iff' (n : ℕ) : True := trivial\n"
                                  "@[simp] lemma foo_bar : True := trivial\nend Nat\n")
        idx = fixer.mathlib_index(d)
        self.assertIn("Nat.succ_le_iff'", idx)
        self.assertIn("Nat.foo_bar", idx)


if __name__ == "__main__":
    unittest.main()
