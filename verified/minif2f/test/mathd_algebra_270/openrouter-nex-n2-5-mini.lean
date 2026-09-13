import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h₁ : f 1 = 1 / 3 := by
    have h₁' : (1 : ℝ) ≠ -2 := by norm_num
    have h₁'' : f 1 = 1 / ((1 : ℝ) + 2) := h₀ 1 h₁'
    norm_num at h₁''
    exact h₁''

  have h₂ : f (f 1) = 3 / 7 := by
    have h₂' : f 1 ≠ -2 := by
      rw [h₁]
      norm_num
    have h₂'' : f (f 1) = 1 / (f 1 + 2) := h₀ (f 1) h₂'
    rw [h₂'', h₁]
    norm_num

  exact h₂
