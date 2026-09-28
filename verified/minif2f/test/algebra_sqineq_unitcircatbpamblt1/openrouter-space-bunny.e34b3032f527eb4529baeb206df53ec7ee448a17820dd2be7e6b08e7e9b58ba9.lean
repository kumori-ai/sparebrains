import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have ha : a ≤ 1 := by
    nlinarith [sq_nonneg b]
  have hb : -1 ≤ b := by
    nlinarith [sq_nonneg a]
  have hprod : 0 ≤ (1 - a) * (1 + b) :=
    mul_nonneg (sub_nonneg.mpr ha) (by linarith)
  nlinarith
