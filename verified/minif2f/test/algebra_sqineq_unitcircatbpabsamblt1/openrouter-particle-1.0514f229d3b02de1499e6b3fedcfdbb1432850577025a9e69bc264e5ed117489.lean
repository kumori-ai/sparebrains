import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have h_ab_le : a * b ≤ 1 / 2 := by
    nlinarith [sq_nonneg (a - b), h₀]
  have h_nonneg : 0 ≤ 1 - a * b := by
    nlinarith
  have h_sq : (a - b) ^ 2 ≤ (1 - a * b) ^ 2 := by
    nlinarith [sq_nonneg (a * b), h₀]
  have h_abs : |a - b| ≤ 1 - a * b := by
    have h := (sq_le_sq.mp h_sq)
    rw [abs_of_nonneg h_nonneg] at h
    exact h
  rw [Real.norm_eq_abs]
  linarith
