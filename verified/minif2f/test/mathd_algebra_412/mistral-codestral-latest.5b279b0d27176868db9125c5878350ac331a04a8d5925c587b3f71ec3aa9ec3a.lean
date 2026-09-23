import Mathlib

open scoped Nat
open scoped Real

/--
The sum of two numbers is 25 and their difference is 11. What is the larger of the two numbers? -/
theorem mathd_algebra_412 (x y : ℝ) (h₀ : x + y = 25) (h₁ : x - y = 11) : x = 18 := by
  have h₂ : 2 * x = 36 := by linarith [h₀, h₁]
  linarith [h₂]
