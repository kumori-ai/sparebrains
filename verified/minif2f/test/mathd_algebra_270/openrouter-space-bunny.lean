import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h₁ : f 1 = 1 / 3 := by
    calc
      f 1 = 1 / (1 + 2) := h₀ 1 (by norm_num)
      _ = 1 / 3 := by norm_num
  calc
    f (f 1) = f (1 / 3) := by rw [h₁]
    _ = 1 / (1 / 3 + 2) := h₀ (1 / 3 : ℝ) (by norm_num)
    _ = 3 / 7 := by norm_num
