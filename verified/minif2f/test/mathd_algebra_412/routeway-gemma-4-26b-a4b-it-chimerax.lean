import Mathlib

open scoped Nat
open scoped Real

/--
The sum of two numbers is 25 and their difference is 11. What is the larger of the two numbers? -/
theorem mathd_algebra_412 (x y : ℝ) (h₀ : x + y = 25) (h₁ : x - y = 11) : x = 18 := by
  have h_sum_diff : (x + y) + (x - y) = 25 + 11 := by
    rw [h₀, h₁]
  have h_two_x : 2 * x = 36 := by
    rw [← add_sub_cancel_right x y, ← add_sub_cancel_right x y] at h_sum_diff
    linarith
  have h_two_x_half : x = 18 := by
    field_simp at h_two_x
    linarith
  exact h_two_x_half
