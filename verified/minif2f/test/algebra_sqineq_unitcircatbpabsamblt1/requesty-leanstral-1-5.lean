import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have h_sq_eq : (a - b) ^ 2 = (‖a - b‖) ^ 2 := by
    simp [Real.norm_eq_abs, sq_abs]
  have h_eq_mul : 2 * (1 - a * b - ‖a - b‖) = (‖a - b‖ - 1) ^ 2 := by
    calc
      2 * (1 - a * b - ‖a - b‖) = 2 * ((a ^ 2 + b ^ 2) - a * b - ‖a - b‖) := by rw [h₀]
      _ = 2 * (a ^ 2 + b ^ 2 - a * b) - 2 * ‖a - b‖ := by ring
      _ = ((a - b) ^ 2 + (a ^ 2 + b ^ 2)) - 2 * ‖a - b‖ := by ring
      _ = ((‖a - b‖) ^ 2 + 1) - 2 * ‖a - b‖ := by
        rw [h_sq_eq, h₀]
      _ = (‖a - b‖ - 1) ^ 2 := by ring
  have h_nonneg : 0 ≤ 1 - a * b - ‖a - b‖ := by
    have h_sq_nonneg : 0 ≤ (‖a - b‖ - 1) ^ 2 := sq_nonneg _
    linarith
  linarith
