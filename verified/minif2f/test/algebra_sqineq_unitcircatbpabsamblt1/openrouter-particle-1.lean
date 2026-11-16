import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  have h₁ : (|a - b|) ^ 2 = 1 - 2 * a * b := by
    rw [sq_abs]
    nlinarith [h₀]
  have h₂ : 0 ≤ (|a - b| - 1) ^ 2 := sq_nonneg _
  nlinarith [h₁, h₂]
