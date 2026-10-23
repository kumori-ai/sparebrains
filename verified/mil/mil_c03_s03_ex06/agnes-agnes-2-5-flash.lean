import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra h'
  push_neg at h'
  have h_pos : 0 < x := h'
  have : x < x / 2 := h (x / 2) (by linarith)
  linarith
