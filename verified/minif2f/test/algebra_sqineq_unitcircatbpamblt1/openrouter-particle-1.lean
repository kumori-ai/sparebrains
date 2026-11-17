import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  nlinarith [sq_nonneg (a - b - 1), h₀]
