import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex01 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε hε hε1 hx hy
  rw [abs_mul]
  have hε0 : 0 ≤ ε := hε.le
  have hy0 : 0 ≤ |y| := abs_nonneg y
  by_cases hyz : |y| = 0
  · rw [hyz, mul_zero]
    exact hε
  · have hypos : 0 < |y| := lt_of_le_of_ne hy0 (Ne.symm hyz)
    calc |x| * |y| < ε * |y| := mul_lt_mul_of_pos_right hx hypos
      _ ≤ ε * ε := mul_le_mul_of_nonneg_left hy.le hε0
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hε1 hε0
      _ = ε := mul_one ε
