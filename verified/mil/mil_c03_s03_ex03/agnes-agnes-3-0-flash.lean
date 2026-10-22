import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex03 (a b : ℝ) (f : ℝ → ℝ) (h : Monotone f) (h' : f a < f b) : a < b := by
  by_contra h_contra
  push_neg at h_contra
  have h_ab : b ≤ a := h_contra
  have h_f_le : f b ≤ f a := h h_ab
  have h_absurd : f a < f a := lt_of_lt_of_le h' h_f_le
  exact lt_irrefl _ h_absurd
