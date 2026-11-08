import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have hab : a * b ≤ 1 / 2 := by nlinarith [sq_nonneg (a - b)]
  have h1 : (0 : ℝ) ≤ 1 - a * b := by linarith
  have hsq : (a - b) ^ 2 ≤ (1 - a * b) ^ 2 := by nlinarith [sq_nonneg (a * b)]
  have habs : |a - b| ≤ 1 - a * b := abs_le_of_sq_le_sq hsq h1
  rw [Real.norm_eq_abs]
  linarith
