import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra hx
  have hxpos : 0 < x := lt_of_not_ge hx
  have hxhalf_pos : x / 2 > 0 := by linarith
  have hxlt : x < x / 2 := h (x / 2) hxhalf_pos
  have hxhalf_le : x / 2 ≤ x := by linarith
  linarith
