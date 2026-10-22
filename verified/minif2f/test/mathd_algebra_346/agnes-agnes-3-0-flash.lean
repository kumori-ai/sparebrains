import Mathlib

open scoped Nat
open scoped Real

/-- Let $f(x) = 2x-3$ and $g(x) = x+1$. What is the value of $g(f(5)-1)$? -/
theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
  have h_f5 : f 5 = 7 := by
    calc
      f 5 = 2 * (5 : ℝ) - 3 := by rw [h₀]
      _ = 7 := by norm_num
  have h_g : g (f 5 - 1) = (f 5 - 1) + 1 := by
    rw [h₁]
  calc
    g (f 5 - 1) = (f 5 - 1) + 1 := h_g
    _ = 7 := by
      rw [h_f5]
      ring
