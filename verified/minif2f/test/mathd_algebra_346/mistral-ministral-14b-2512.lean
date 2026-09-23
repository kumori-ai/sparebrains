import Mathlib

open scoped Nat
open scoped Real

/-- Let $f(x) = 2x-3$ and $g(x) = x+1$. What is the value of $g(f(5)-1)$? -/
theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
  have hf5 : f 5 = 2 * 5 - 3 := by rw [h₀]
  have hf5_val : f 5 = 7 := by rw [hf5]; ring_nf
  have hf5_minus1 : f 5 - 1 = 6 := by linarith [hf5_val]
  have hg6 : g 6 = 6 + 1 := by rw [h₁]
  rw [hf5_minus1, hg6]
  ring_nf
