import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have h_sq : ‖a - b‖ ^ 2 = (a - b) ^ 2 := by
    exact sq_abs (a - b)
  have h_exp : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring
  have h_combined : ‖a - b‖ ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
    rw [h_sq, h_exp]
  have h_ab : a * b = (1 - ‖a - b‖ ^ 2) / 2 := by
    linarith [h_combined, h₀]
  calc
    a * b + ‖a - b‖ = (1 - ‖a - b‖ ^ 2) / 2 + ‖a - b‖ := by rw [h_ab]
    _ = (2 - (‖a - b‖ - 1) ^ 2) / 2 := by ring
    _ ≤ 1 := by
      have h_nonneg : 0 ≤ (‖a - b‖ - 1) ^ 2 := by positivity
      linarith
