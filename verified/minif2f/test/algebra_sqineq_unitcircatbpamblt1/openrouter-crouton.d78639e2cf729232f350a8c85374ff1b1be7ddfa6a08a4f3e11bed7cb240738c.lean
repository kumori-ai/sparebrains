import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have hsq : (0 : ℝ) ≤ (a - b - 1) ^ 2 := sq_nonneg _
  have h1 : (a - b - 1) ^ 2 = a ^ 2 + b ^ 2 - 2 * (a * b) - 2 * a + 2 * b + 1 := by ring
  rw [h₀] at h1
  linarith
