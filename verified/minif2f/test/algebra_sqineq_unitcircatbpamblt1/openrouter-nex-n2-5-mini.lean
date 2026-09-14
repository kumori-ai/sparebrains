import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have ha : a ≤ 1 := by
    nlinarith
  have hb : b ≥ -1 := by
    nlinarith
  have h : 0 ≤ (1 - a) * (1 + b) := by
    nlinarith
  calc
    a * b + (a - b) = 1 - (1 - a) * (1 + b) := by ring
    _ ≤ 1 := by linarith
