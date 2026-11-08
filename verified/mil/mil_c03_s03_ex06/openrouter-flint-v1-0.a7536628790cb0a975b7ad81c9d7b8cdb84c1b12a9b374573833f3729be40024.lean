import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra hnot
  have hx : 0 < x := lt_of_not_ge hnot
  have hε2_pos : x / 2 > 0 := div_pos hx (by norm_num)
  have hlt : x < x / 2 := h (x / 2) hε2_pos
  have hε2_lt_x : x / 2 < x := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    rw [div_lt_iff₀ h2]
    have hmul : x * 2 = x + x := by ring
    rw [hmul]
    linarith
  have hlt' : x < x := lt_trans hlt hε2_lt_x
  exact (lt_irrefl x) hlt'
