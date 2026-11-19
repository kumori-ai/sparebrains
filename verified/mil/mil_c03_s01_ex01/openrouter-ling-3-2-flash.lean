import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex01 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε hε0 hε1 hx hy
  rw [abs_mul]
  have hy1 : |y| ≤ 1 := (lt_of_lt_of_le hy hε1).le
  have h2 : |x| * |y| ≤ |x| * 1 := mul_le_mul_of_nonneg_left hy1 (abs_nonneg x)
  rw [mul_one] at h2
  linarith
