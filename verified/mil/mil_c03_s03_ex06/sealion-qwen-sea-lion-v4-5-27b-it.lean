import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra h'
  have h_pos : x > 0 := lt_of_not_ge h'
  have h_contra : x < x := h x h_pos
  exact lt_irrefl x h_contra
