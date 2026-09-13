import Mathlib

open scoped Nat
open scoped Real

/-- If $3a + b + c = -3, a+3b+c = 9, a+b+3c = 19$, then find $abc$. -/
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have h3 : a - b = -6 := by linarith
  have h4 : b - c = -5 := by linarith
  have h5 : b = 2 := by linarith [h3, h4, h₀]
  have h6 : a = -4 := by linarith [h3, h5]
  have h7 : c = 7 := by linarith [h4, h5]
  rw [h6, h5, h7]
  norm_num
