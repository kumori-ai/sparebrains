import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have h1 : 0 ≤ 1 - a * b := by nlinarith [sq_nonneg (a - b), h₀]
  have heq : (1 - a * b) ^ 2 - (a - b) ^ 2 = (a * b) ^ 2 := by linear_combination -h₀
  have h2 : (a - b) ^ 2 ≤ (1 - a * b) ^ 2 := by linarith [sq_nonneg (a * b)]
  have h3 : |a - b| ≤ 1 - a * b := abs_le_of_sq_le_sq h2 h1
  rw [Real.norm_eq_abs]
  linarith
