import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h₁ : f 1 = 1 / 3 := by
    have h₁' : (1 : ℝ) ≠ -2 := by norm_num
    rw [h₀ 1 h₁']
    norm_num
  have h₂ : f (f 1) = 3 / 7 := by
    rw [h₁]
    have h₂' : (1 / 3 : ℝ) ≠ -2 := by norm_num
    rw [h₀ (1 / 3) h₂']
    norm_num
  exact h₂
