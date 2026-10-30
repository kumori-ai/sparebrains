import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex03 (a b : ℝ) (f : ℝ → ℝ) (h : Monotone f) (h' : f a < f b) : a < b := by
  by_contra h_ab
  have h_ge : b ≤ a := not_lt.mp h_ab
  have h_f : f b ≤ f a := h h_ge
  exact lt_irrefl (f b) (lt_of_le_of_lt h_f h')
