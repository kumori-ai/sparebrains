import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = x + 1$ and $g(x) = x^2 + 3$, what is the value of $f(g(2))$? -/
theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  have h₂ : g 2 = 2 ^ 2 + 3 := by
    rw [h₁]
  have h₃ : g 2 = 7 := by
    rw [h₂]
    norm_num
  have h₄ : f (g 2) = g 2 + 1 := by
    rw [h₀]
  rw [h₄, h₃]
  norm_num
