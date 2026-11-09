import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h1 : (1 : ℝ) ≠ -2 := by norm_num
  have hf1 : f 1 = 1 / 3 := by
    rw [h₀ 1 h1]
    norm_num
  have h2 : (1 / 3 : ℝ) ≠ -2 := by norm_num
  rw [hf1, h₀ (1 / 3) h2]
  norm_num
