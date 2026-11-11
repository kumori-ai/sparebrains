import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex03 (a b : ℝ) (f : ℝ → ℝ) (h : Monotone f) (h' : f a < f b) : a < b := by
  by_contra hle
  have hba : b ≤ a := not_lt.mp hle
  have hfba : f b ≤ f a := h hba
  exact (not_le_of_gt h') hfba
