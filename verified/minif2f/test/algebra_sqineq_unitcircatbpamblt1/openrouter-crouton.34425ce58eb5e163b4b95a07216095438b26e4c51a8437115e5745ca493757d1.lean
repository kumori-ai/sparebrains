import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have hsq : 0 ≤ (a - b - 1) ^ 2 := sq_nonneg _
  have h1 : (a - b - 1) ^ 2 = 2 - 2 * (a * b) - 2 * a + 2 * b := by
    calc (a - b - 1) ^ 2 = (a ^ 2 + b ^ 2) + 1 - 2 * (a * b) - 2 * a + 2 * b := by ring
      _ = 2 - 2 * (a * b) - 2 * a + 2 * b := by rw [h₀]; ring
  linarith [hsq, h1]
