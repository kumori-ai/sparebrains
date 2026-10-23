import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have h₁ : (a - b) ^ 2 = 1 - 2 * a * b := by
    nlinarith
  have h₂ : a * b + (a - b) ≤ 1 := by
    nlinarith [sq_nonneg (a - b - 1)]
  exact h₂
