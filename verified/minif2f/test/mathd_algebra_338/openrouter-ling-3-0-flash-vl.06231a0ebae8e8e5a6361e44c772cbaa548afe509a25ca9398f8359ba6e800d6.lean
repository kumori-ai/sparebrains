import Mathlib

open scoped Nat
open scoped Real

/-- If $3a + b + c = -3, a+3b+c = 9, a+b+3c = 19$, then find $abc$. -/
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have h_sub1 : b - a = 6 := by
    linarith [h₀, h₁]
  have h_sub2 : c - b = 5 := by
    linarith [h₁, h₂]
  have h_sum : a + b + c = 5 := by
    linarith [h₀, h₁, h₂]
  have h_a : a = -4 := by
    linarith [h_sub1, h_sub2, h_sum]
  have h_b : b = 2 := by
    linarith [h_a, h_sub1]
  have h_c : c = 7 := by
    linarith [h_b, h_sub2]
  rw [h_a, h_b, h_c]
  norm_num
