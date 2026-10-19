import Mathlib

open scoped Nat
open scoped Real

/--
Find the positive solution to \[ \frac 1{x^2-10x-29}+\frac1{x^2-10x-45}-\frac 2{x^2-10x-69}=0 \] -/
theorem aime_1990_p4 (x : ℝ) (h₀ : 0 < x) (h₁ : x ^ 2 - 10 * x - 29 ≠ 0)
    (h₂ : x ^ 2 - 10 * x - 45 ≠ 0) (h₃ : x ^ 2 - 10 * x - 69 ≠ 0)
    (h₄ : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69) = 0) :
    x = 13 := by
  let D := x ^ 2 - 10 * x
  let num := (D - 45) * (D - 69) + (D - 29) * (D - 69) - 2 * (D - 29) * (D - 45)
  have num_eq_zero : num = 0 := by
    grind
  have eq_num : (D - 13) * (D - 39) = 0 := by
    nlinarith
  nlinarith