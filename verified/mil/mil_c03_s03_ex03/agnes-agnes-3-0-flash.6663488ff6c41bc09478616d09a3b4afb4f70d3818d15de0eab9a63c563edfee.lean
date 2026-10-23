import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex03 (a b : ℝ) (f : ℝ → ℝ) (h : Monotone f) (h' : f a < f b) : a < b := by
  by_contra h_contra
  push_neg at h_contra
  have h_ab : b ≤ a := by
    by_contra h_neq
    push_neg at h_neq
    linarith
  have h_f : f b ≤ f a := h h_ab
  linarith
