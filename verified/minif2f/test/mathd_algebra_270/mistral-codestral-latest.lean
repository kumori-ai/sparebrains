import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h₁ : (1 : ℝ) ≠ -2 := by norm_num
  have h₂ : f 1 = 1 / (1 + 2) := h₀ 1 h₁
  have h₃ : f (1 / (1 + 2)) = 1 / (1 / (1 + 2) + 2) := h₀ (1 / (1 + 2)) (by norm_num)
  rw [h₂, h₃]
  field_simp
  ring
