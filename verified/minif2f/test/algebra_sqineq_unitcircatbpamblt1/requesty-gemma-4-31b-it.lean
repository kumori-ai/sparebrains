import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have h_sq : (a - b - 1)^2 = 2 - 2 * (a * b + a - b) := by
    calc (a - b - 1)^2 = a^2 + b^2 + 1 - 2 * a * b - 2 * a + 2 * b := by ring
    _ = 1 + 1 - 2 * a * b - 2 * a + 2 * b := by rw [h₀]
    _ = 2 - 2 * (a * b + a - b) := by ring
  have h_nonneg : (a - b - 1)^2 ≥ 0 := pow_two_nonneg (a - b - 1)
  rw [h_sq] at h_nonneg
  linarith
