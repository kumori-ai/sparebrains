import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have h₁ : a ≤ 1 := by
    nlinarith [sq_nonneg b]
  have h₂ : b ≥ -1 := by
    nlinarith [sq_nonneg a]
  have h₃ : (a - 1) * (b + 1) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  nlinarith [h₃]
