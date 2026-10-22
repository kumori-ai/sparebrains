import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex03 (a b : ℝ) (f : ℝ → ℝ) (h : Monotone f) (h' : f a < f b) : a < b := by
  by_contra hnot
  have hba : b ≤ a := le_of_not_gt hnot
  have hfbfa : f b ≤ f a := h hba
  exact (lt_irrefl (f b)) (hfbfa.trans_lt h')
