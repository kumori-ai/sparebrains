"""tools/reachable.py: a published proof counts only for the statement we hold. Notation-only differences pass
(`∑ k in` for `∑ k ∈`, parentheses, spacing); a weaker or leaked statement does not."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import reachable as rc

OURS = "theorem t (x : ℝ) (h₀ : 0 < x) :\n    (∑ k ∈ Finset.Icc 1 20, x ^ k) = 21000 := by\n  sorry\n"


class Statements(unittest.TestCase):
    def test_the_statement_is_everything_between_the_name_and_the_proof(self):
        self.assertEqual(rc.statement(OURS, "t"), "(x : ℝ) (h₀ : 0 < x) : (∑ k ∈ Finset.Icc 1 20, x ^ k) = 21000")
        self.assertIsNone(rc.statement("lemma other : True := trivial", "t"))

    def test_notation_only_differences_match_and_a_weaker_statement_does_not(self):
        same = "theorem t (x : ℝ) (h₀ : 0 < x) : ∑ k in Finset.Icc 1 20, x ^ k = 21000 := by\n  simp"
        weaker = "theorem t (x : ℝ) (h₀ : 0 < x) : (∑ k ∈ Finset.Icc 1 20, x ^ k) ≤ 21000 := by\n  simp"
        self.assertEqual(rc.match(rc.statement(OURS, "t"), rc.statement(OURS + "\n", "t")), "exact")
        self.assertEqual(rc.match(rc.statement(OURS, "t"), rc.statement(same, "t")), "notation")
        self.assertIsNone(rc.match(rc.statement(OURS, "t"), rc.statement(weaker, "t")))
        self.assertIsNone(rc.match(rc.statement(OURS, "t"), None))

    def test_each_target_lists_who_proved_its_statement(self):
        ours = {"t": OURS, "u": "theorem u : 1 = 1 := by\n  sorry\n"}
        published = {"DeepSeek-Prover-V2": {"t": "theorem t (x : ℝ) (h₀ : 0 < x) : ∑ k in Finset.Icc 1 20, x ^ k = 21000 := by simp"},
                     "Kimina-Prover": {"u": "theorem u : 2 = 2 := by rfl"}}
        out = rc.compare(ours, published)
        self.assertEqual(out["t"], {"DeepSeek-Prover-V2": "notation"})
        self.assertEqual(out["u"], {"Kimina-Prover": None}, "proved, but a different statement")


if __name__ == "__main__":
    unittest.main()
