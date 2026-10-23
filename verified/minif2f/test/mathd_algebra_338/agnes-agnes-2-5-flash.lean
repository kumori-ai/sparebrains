import Mathlib

open scoped Nat
open scoped Real

/-- If $3a + b + c = -3, a+3b+c = 9, a+b+3c = 19$, then find $abc$. -/
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have h₃ : a = -4 := by
    have h₃a : 5 * a + 5 * b + 5 * c = 25 := by
      linarith
    have h₃b : a + b + c = 5 := by linarith
    linarith
  have h₄ : b = 2 := by
    have h₄a : a + b + c = 5 := by
      have h₄b : 5 * a + 5 * b + 5 * c = 25 := by linarith
      linarith
    linarith
  have h₅ : c = 7 := by
    have h₅a : a + b + c = 5 := by
      have h₅b : 5 * a + 5 * b + 5 * c = 25 := by linarith
      linarith
    linarith
  rw [h₃, h₄, h₅]
  norm_num
