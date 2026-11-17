import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex01 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε hε hε1 hx hy
  rw [abs_mul]
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have h1 : |x| * |y| < ε * ε := by
    calc
      |x| * |y| ≤ |x| * ε := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hy) hx0
      _ < ε * ε := by
        exact mul_lt_mul_of_pos_right hx hε
  have h2 : ε * ε ≤ ε := by
    nlinarith [hε.le, hε1]
  exact lt_of_lt_of_le h1 h2
