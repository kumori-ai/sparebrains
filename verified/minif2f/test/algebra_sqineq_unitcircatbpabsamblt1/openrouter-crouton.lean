import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  have h1 : (a - b) ^ 2 = 1 - 2 * (a * b) := by
    have h : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * (a * b) := by ring
    rw [h₀] at h
    linarith
  have h2 : (a - b) ^ 2 = |a - b| ^ 2 := by rw [sq_abs]
  have hab : a * b = (1 - |a - b| ^ 2) / 2 := by linarith
  rw [hab]
  have h3 : (1 - |a - b| ^ 2) / 2 + |a - b| = 1 - (|a - b| - 1) ^ 2 / 2 := by ring
  rw [h3]
  have h4 : 0 ≤ (|a - b| - 1) ^ 2 / 2 :=
    div_nonneg (sq_nonneg _) (by norm_num)
  linarith
