import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have h₁ : (a - b) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (a + b)]
  have h₂ : a * b = (1 - (a - b) ^ 2) / 2 := by
    linarith
  have h₃ : a * b + (a - b) = (1 - (a - b) ^ 2) / 2 + (a - b) := by
    rw [h₂]
  have h₄ : (1 - (a - b) ^ 2) / 2 + (a - b) ≤ 1 := by
    nlinarith [sq_nonneg (a - b - 1)]
  linarith
