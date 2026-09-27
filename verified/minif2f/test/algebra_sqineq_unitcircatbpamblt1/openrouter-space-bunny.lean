import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have h : 0 ≤ (a - b - 1) ^ 2 := sq_nonneg _
  nlinarith [h₀, h]
