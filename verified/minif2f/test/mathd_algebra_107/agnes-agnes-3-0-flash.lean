import Mathlib

open scoped Nat
open scoped Real

/-- Find the radius of the circle with equation $x^2 + 8x + y^2 - 6y = 0$. -/
theorem mathd_algebra_107 (x y : ℝ) (h₀ : x ^ 2 + 8 * x + y ^ 2 - 6 * y = 0) :
    (x + 4) ^ 2 + (y - 3) ^ 2 = 5 ^ 2 := by
  have h₁ : (x + 4) ^ 2 = x ^ 2 + 8 * x + 16 := by
    ring
  have h₂ : (y - 3) ^ 2 = y ^ 2 - 6 * y + 9 := by
    ring
  have h₃ : (x + 4) ^ 2 + (y - 3) ^ 2 = x ^ 2 + 8 * x + y ^ 2 - 6 * y + 25 := by
    rw [h₁, h₂]
    ring
  rw [h₃]
  have h₄ : x ^ 2 + 8 * x + y ^ 2 - 6 * y + 25 = 25 := by
    rw [h₀]
    norm_num
  rw [h₄]
  ring
