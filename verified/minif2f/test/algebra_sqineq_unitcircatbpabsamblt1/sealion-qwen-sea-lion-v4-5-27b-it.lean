import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have h₁ : ‖a - b‖ ^ 2 = 1 - 2 * a * b := by
    calc
      ‖a - b‖ ^ 2 = |a - b| ^ 2 := by rfl
      _ = (a - b) ^ 2 := by rw [sq_abs]
      _ = a ^ 2 - 2 * a * b + b ^ 2 := by ring
      _ = (a ^ 2 + b ^ 2) - 2 * a * b := by ring
      _ = 1 - 2 * a * b := by rw [h₀]
  nlinarith [h₁, sq_nonneg (‖a - b‖ - 1)]
