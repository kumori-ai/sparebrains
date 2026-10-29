import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  calc
  a * (2 - a) = 1 - (a - 1) ^ 2 := by ring
  _ ≤ 1 := by linarith [sq_nonneg (a - 1)]
