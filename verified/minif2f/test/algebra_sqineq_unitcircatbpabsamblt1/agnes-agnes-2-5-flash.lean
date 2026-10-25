import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have h₁ : -1 ≤ a ∧ a ≤ 1 := by
    constructor
    · nlinarith [sq_nonneg b]
    · nlinarith [sq_nonneg b]
  have h₂ : -1 ≤ b ∧ b ≤ 1 := by
    constructor
    · nlinarith [sq_nonneg a]
    · nlinarith [sq_nonneg a]
  by_cases h₃ : a ≥ b
  · have h₄ : ‖a - b‖ = a - b := by
      rw [show ‖a - b‖ = abs (a - b) by simp]
      rw [abs_of_nonneg (by linarith)]
    rw [h₄]
    nlinarith
  · have h₄ : ‖a - b‖ = b - a := by
      rw [show ‖a - b‖ = abs (a - b) by simp]
      have h₅ : a - b ≤ 0 := by linarith
      rw [abs_of_nonpos h₅]
      ring
    rw [h₄]
    nlinarith
