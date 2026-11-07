import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have hsq : (a - b - 1)^2 ≥ 0 := sq_nonneg _
  have h_eq : (a - b - 1)^2 = 2 * (1 - (a * b + (a - b))) := by
    calc
      (a - b - 1)^2 = (a - b)^2 - 2*(a - b) + 1 := by ring
      _ = (a^2 + b^2) - 2*a*b - 2*a + 2*b + 1 := by ring
      _ = 1 - 2*a*b - 2*a + 2*b + 1 := by rw [h₀]
      _ = 2*(1 - (a*b + a - b)) := by ring
      _ = 2 * (1 - (a * b + (a - b))) := by ring
  have htemp : 0 ≤ 2 * (1 - (a * b + (a - b))) := by
    rw [← h_eq]
    exact hsq
  linarith
