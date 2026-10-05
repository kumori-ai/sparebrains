import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex01 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε hε hε1 hx hy
  by_cases hy0 : y = 0
  · rw [hy0]
    simp [abs_zero, mul_zero, hε]
  · have : 0 < |y| := abs_pos.mpr hy0
    calc
      |x * y| = |x| * |y| := by rw [abs_mul]
      _ < ε * |y| := mul_lt_mul_of_pos_right hx this
      _ < ε * ε := mul_lt_mul_of_pos_left hy (by positivity)
      _ ≤ ε := by
        have : ε * ε ≤ ε * 1 := mul_le_mul_of_nonneg_left hε1 (by linarith)
        simpa [mul_one] using this
