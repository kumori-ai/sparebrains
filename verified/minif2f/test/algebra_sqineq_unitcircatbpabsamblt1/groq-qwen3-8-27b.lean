import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have h₁ : (a - b) ^ 2 = 1 - 2 * a * b := by
    nlinarith [h₀]
  have h₂ : ‖a - b‖ ^ 2 = (a - b) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  have h₃ : ‖a - b‖ ^ 2 = 1 - 2 * a * b := by
    rw [h₂, h₁]
  have h₄ : a * b = (1 - ‖a - b‖ ^ 2) / 2 := by
    nlinarith [h₃]
  have h₅ : a * b + ‖a - b‖ = (1 - ‖a - b‖ ^ 2) / 2 + ‖a - b‖ := by
    rw [h₄]
  have h₆ : (1 - ‖a - b‖ ^ 2) / 2 + ‖a - b‖ = (2 - (‖a - b‖ - 1) ^ 2) / 2 := by
    ring
  have h₇ : (2 - (‖a - b‖ - 1) ^ 2) / 2 ≤ 1 := by
    have h₇₁ : (‖a - b‖ - 1) ^ 2 ≥ 0 := by nlinarith
    nlinarith [h₇₁]
  calc
    a * b + ‖a - b‖ = (1 - ‖a - b‖ ^ 2) / 2 + ‖a - b‖ := h₅
    _ = (2 - (‖a - b‖ - 1) ^ 2) / 2 := h₆
    _ ≤ 1 := h₇
