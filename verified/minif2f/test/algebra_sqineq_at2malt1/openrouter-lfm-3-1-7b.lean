import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have eq : a * (2 - a) = 1 - (a - 1) ^ 2 := by ring
  rw [eq]
  have h : (a - 1) ^ 2 ≥ 0 := sq_nonneg (a - 1)
  linarith [h]
