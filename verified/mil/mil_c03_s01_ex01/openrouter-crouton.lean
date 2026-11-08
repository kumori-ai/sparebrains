import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex01 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε hε hε1 hx hy
  rw [abs_mul]
  calc |x| * |y| < ε * ε := mul_lt_mul'' hx hy (abs_nonneg x) (abs_nonneg y)
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hε1 (le_of_lt hε)
    _ = ε := mul_one ε
