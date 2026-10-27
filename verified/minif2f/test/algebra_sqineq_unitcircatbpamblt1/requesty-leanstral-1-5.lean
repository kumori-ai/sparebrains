import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have ha_sq_le : a ^ 2 ≤ 1 := by
    have hb_sq_nonneg : b ^ 2 ≥ 0 := sq_nonneg b
    linarith
  have hb_sq_le : b ^ 2 ≤ 1 := by
    have ha_sq_nonneg : a ^ 2 ≥ 0 := sq_nonneg a
    linarith
  have ha_le_one : a ≤ 1 := by
    by_contra! h
    nlinarith
  have hb_ge_neg_one : -1 ≤ b := by
    by_contra! h
    nlinarith
  have h_nonpos : (a - 1) * (b + 1) ≤ 0 := by
    have h1 : a - 1 ≤ 0 := by linarith
    have h2 : 0 ≤ b + 1 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg h1 h2
  have h_eq : a * b + (a - b) - 1 = (a - 1) * (b + 1) := by ring
  linarith
