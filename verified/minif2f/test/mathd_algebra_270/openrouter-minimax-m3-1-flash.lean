import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h₁ : f 1 = 1 / 3 := by
    have h := h₀ 1 (by norm_num : (1 : ℝ) ≠ -2)
    norm_num at h
    exact h
  calc
    f (f 1) = f (1 / 3) := congrArg f h₁
    _ = 1 / (1 / 3 + 2) := h₀ (1 / 3) (by norm_num : (1 / 3 : ℝ) ≠ -2)
    _ = 3 / 7 := by norm_num
