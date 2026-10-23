import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra h'
  let ε := x - 0
  have hε : ε > 0 := sub_pos_of_lt (not_le.mp h')
  have hcontra := h ε hε
  linarith
