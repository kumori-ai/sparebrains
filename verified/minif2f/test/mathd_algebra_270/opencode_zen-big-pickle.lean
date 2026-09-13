import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h1 : f 1 = 1 / 3 := by
    have h1ne : (1 : ℝ) ≠ -2 := by norm_num
    rw [h₀ 1 h1ne]
    norm_num
  have h2 : f 1 ≠ -2 := by
    rw [h1]
    norm_num
  calc
    f (f 1) = 1 / (f 1 + 2) := h₀ (f 1) h2
    _ = 1 / (1 / 3 + 2) := by rw [h1]
    _ = 3 / 7 := by norm_num
