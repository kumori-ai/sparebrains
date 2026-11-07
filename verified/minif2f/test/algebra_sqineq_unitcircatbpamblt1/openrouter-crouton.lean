import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have key : 2 * (1 - (a * b + (a - b))) = (a - b - 1) ^ 2 := by
    linear_combination -h₀
  have hnn : 0 ≤ (a - b - 1) ^ 2 := sq_nonneg (a - b - 1)
  linarith
