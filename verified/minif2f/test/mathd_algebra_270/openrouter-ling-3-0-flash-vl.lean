import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h₁ : f 1 = 1 / 3 := by
    have h := h₀ 1 (by norm_num)
    norm_num at h
    exact h
  have h₂ : f 1 ≠ -2 := by
    rw [h₁]
    norm_num
  have h₃ : f (f 1) = 1 / (f 1 + 2) := h₀ (f 1) h₂
  rw [h₁] at h₃
  norm_num at h₃
  rw [h₁]
  exact h₃
