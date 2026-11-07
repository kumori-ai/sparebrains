import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have hd_sq : (a - b) ^ 2 = 1 - 2 * a * b := by
    nlinarith
  have hab : a * b = (1 - (a - b) ^ 2) / 2 := by
    nlinarith
  rw [hab]
  by_cases hd : a - b ≥ 0
  · have habs : ‖a - b‖ = a - b := by
      simpa [Real.norm_eq_abs] using abs_of_nonneg hd
    rw [habs]
    have htemp : ((1 - (a - b) ^ 2) / 2) + (a - b) ≤ 1 := by
      have h : ((1 - (a - b) ^ 2) / 2) + (a - b) - 1 ≤ 0 := by
        field_simp
        nlinarith
      linarith
    exact htemp
  · have hd' : a - b < 0 := by linarith
    have habs : ‖a - b‖ = -(a - b) := by
      simpa [Real.norm_eq_abs] using abs_of_neg hd'
    rw [habs]
    have htemp : ((1 - (a - b) ^ 2) / 2) + (-(a - b)) ≤ 1 := by
      have h : ((1 - (a - b) ^ 2) / 2) + (-(a - b)) - 1 ≤ 0 := by
        field_simp
        nlinarith
      linarith
    exact htemp
