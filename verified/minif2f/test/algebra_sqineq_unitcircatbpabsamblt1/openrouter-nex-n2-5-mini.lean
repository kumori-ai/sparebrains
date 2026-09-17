import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have h₂ : 2 * a * b = 1 - (a - b) ^ 2 := by
    calc
      2 * a * b = (a ^ 2 + b ^ 2) - (a - b) ^ 2 := by ring
      _ = 1 - (a - b) ^ 2 := by rw [h₀]
  have h₃ : a * b = (1 - ‖a - b‖ ^ 2) / 2 := by
    calc
      a * b = (2 * a * b) / 2 := by ring
      _ = (1 - (a - b) ^ 2) / 2 := by rw [h₂]
      _ = (1 - ‖a - b‖ ^ 2) / 2 := by
        have h₄ : (a - b) ^ 2 = ‖a - b‖ ^ 2 := by simp [Real.norm_eq_abs]
        rw [h₄]
  rw [h₃]
  nlinarith [sq_nonneg (‖a - b‖ - 1)]
