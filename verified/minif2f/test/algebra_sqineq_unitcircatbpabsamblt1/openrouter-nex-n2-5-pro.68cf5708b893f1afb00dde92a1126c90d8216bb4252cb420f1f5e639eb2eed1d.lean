import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have h₁ : a * b ≤ 1 / 2 := by
    nlinarith [sq_nonneg (a - b)]
  have h₂ : 0 ≤ 1 - a * b := by linarith
  have h₃ : (a - b) ^ 2 ≤ (1 - a * b) ^ 2 := by
    nlinarith [h₀]
  have h₄ : ‖a - b‖ ≤ 1 - a * b := by
    rw [Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> nlinarith [h₂, h₃]
  linarith
