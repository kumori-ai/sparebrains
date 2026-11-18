import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have h1 : ‖a - b‖ ^ 2 = (a - b) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (‖a - b‖ - 1)]
