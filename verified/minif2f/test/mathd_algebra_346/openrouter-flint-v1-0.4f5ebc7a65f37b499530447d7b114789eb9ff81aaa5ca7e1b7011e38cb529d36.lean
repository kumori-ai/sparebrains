import Mathlib

open scoped Nat
open scoped Real

/-- Let $f(x) = 2x-3$ and $g(x) = x+1$. What is the value of $g(f(5)-1)$? -/
theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
  have hf : f 5 = 7 := by
    have h₅ := h₀ 5
    rw [h₅]
    norm_num
  have hg : g (f 5 - 1) = 7 := by
    have h_g : g (f 5 - 1) = (f 5 - 1) + 1 := h₁ (f 5 - 1)
    rw [h_g, hf]
    norm_num
  exact hg
