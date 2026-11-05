import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h1 : f 1 = (1 / 3 : ℝ) := by
    have hne : (1 : ℝ) ≠ -2 := by norm_num
    have h := h₀ 1 hne
    norm_num at h
    exact h
  rw [h1]
  have h2 : (1 / 3 : ℝ) ≠ -2 := by norm_num
  have h3 : f (1 / 3) = 1 / (1 / 3 + 2) := h₀ (1 / 3) h2
  rw [h3]
  norm_num
