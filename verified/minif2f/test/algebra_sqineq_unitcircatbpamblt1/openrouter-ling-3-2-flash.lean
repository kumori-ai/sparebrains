import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have h₁ : (a - b - 1) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 - 2 * a + 2 * b + 1 := by ring
  have h₂ : (a - b - 1) ^ 2 ≥ 0 := by positivity
  have h₃ : a ^ 2 - 2 * a * b + b ^ 2 - 2 * a + 2 * b + 1 ≥ 0 := by rw [← h₁]; exact h₂
  linarith
