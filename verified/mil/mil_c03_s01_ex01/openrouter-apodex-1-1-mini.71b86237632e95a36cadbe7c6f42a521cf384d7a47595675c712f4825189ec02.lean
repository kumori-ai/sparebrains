import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex01 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε hε0 hε1 hx hy
  calc
    |x * y| = |x| * |y| := by rw [abs_mul]
    _ ≤ |x| * ε := by
      apply mul_le_mul_of_nonneg_left
      · exact le_of_lt hy
      · exact abs_nonneg x
    _ < ε * ε := by
      apply mul_lt_mul_of_pos_right
      · exact hx
      · exact hε0
    _ ≤ ε := by
      apply mul_le_of_le_one_right (le_of_lt hε0) hε1
