import Mathlib

open scoped Nat
open scoped Real

/-- Let $f(x) = 2x-3$ and $g(x) = x+1$. What is the value of $g(f(5)-1)$? -/
theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
  have h₂ : f 5 = 7 := by
    rw [h₀]
    norm_num
  have h₃ : g (f 5 - 1) = g 6 := by
    rw [h₂]
    <;> ring
  rw [h₃]
  have h₄ : g 6 = 7 := by
    rw [h₁]
    norm_num
  rw [h₄]
