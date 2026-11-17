import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have ha : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  have hb : -1 ≤ b := by nlinarith [sq_nonneg (b + 1)]
  have h₁ : 0 ≤ 1 - a := by linarith
  have h₂ : 0 ≤ 1 + b := by linarith
  have hprod : 0 ≤ (1 - a) * (1 + b) := mul_nonneg h₁ h₂
  nlinarith
