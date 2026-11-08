import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra hx
  have hx_pos : x > 0 := by linarith
  let ε := x / 2
  have ε_pos : 0 < ε := by
    apply div_pos
    · linarith
    · linarith
  have h_lt : x < ε := h ε ε_pos
  have h_contradiction : x < x / 2 := h_lt
  linarith
