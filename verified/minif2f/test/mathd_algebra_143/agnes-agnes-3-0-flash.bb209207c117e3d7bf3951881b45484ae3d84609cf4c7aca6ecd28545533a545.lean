import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = x + 1$ and $g(x) = x^2 + 3$, what is the value of $f(g(2))$? -/
theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  have h₂ : g 2 = 7 := by
    rw [h₁]
    norm_num
  have h₃ : f (g 2) = f 7 := by
    rw [h₂]
  have h₄ : f 7 = 8 := by
    rw [h₀]
    norm_num
  rw [h₃, h₄]
