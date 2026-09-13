import Mathlib

open scoped Nat
open scoped Real

/-- If $3a + b + c = -3, a+3b+c = 9, a+b+3c = 19$, then find $abc$. -/
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have h₃ : a - b = -6 := by linarith [h₀, h₁]
  have h₄ : a - c = -11 := by linarith [h₀, h₂]
  have h₅ : b - c = -5 := by linarith [h₁, h₂]
  have h₆ : a = -4 := by linarith [h₃, h₄]
  have h₇ : b = 2 := by linarith [h₃, h₆]
  have h₈ : c = 7 := by linarith [h₅, h₇]
  rw [h₆, h₇, h₈]
  norm_num
