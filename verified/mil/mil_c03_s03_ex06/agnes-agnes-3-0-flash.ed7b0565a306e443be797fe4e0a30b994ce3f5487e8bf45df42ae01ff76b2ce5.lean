import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < x := hcon
  have hε : 0 < x / 2 := by
    apply div_pos
    · linarith
    · linarith
  have hx : x < x / 2 := h (x / 2) hε
  have hsum : x / 2 + x / 2 = x := by ring
  have hcontra : x < x := by
    have : x < x / 2 + x / 2 := by
      calc
        x < x / 2 := hx
        _ ≤ x / 2 + x / 2 := by linarith [show 0 < x / 2 from hε]
    rw [hsum] at this
    exact this
  linarith [hcontra]
