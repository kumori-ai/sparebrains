import Mathlib

open scoped Nat
open scoped Real

/--
The sum of two numbers is 25 and their difference is 11. What is the larger of the two numbers? -/
theorem mathd_algebra_412 (x y : ℝ) (h₀ : x + y = 25) (h₁ : x - y = 11) : x = 18 := by
  have h₂ : 2 * x = 36 := by
    calc
      2 * x = x + y + (x - y) := by ring
      _ = 36 := by
        rw [h₀, h₁]
        norm_num
  have h₃ : x = 18 := by
    have h₄ : 2 * x = 36 := h₂
    linarith
  exact h₃
