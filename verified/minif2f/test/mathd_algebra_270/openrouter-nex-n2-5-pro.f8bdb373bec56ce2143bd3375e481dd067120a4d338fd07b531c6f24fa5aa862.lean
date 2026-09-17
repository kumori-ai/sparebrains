import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h₁ : f 1 = 1 / 3 := by
    have := h₀ 1 (by norm_num)
    norm_num at this ⊢
    exact this
  rw [h₁]
  have h₂ : f (1 / 3) = 3 / 7 := by
    have := h₀ (1 / 3) (by norm_num)
    norm_num at this ⊢
    exact this
  exact h₂
