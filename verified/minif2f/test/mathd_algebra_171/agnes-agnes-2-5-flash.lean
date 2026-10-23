import Mathlib

open scoped Nat
open scoped Real

/-- Consider the function $f(x)=5x+4$.  What is $f(1)$? -/
theorem mathd_algebra_171 (f : ℝ → ℝ) (h₀ : ∀ x, f x = 5 * x + 4) : f 1 = 9 := by
  have h₁ : f 1 = 5 * 1 + 4 := h₀ 1
  rw [h₁]
  norm_num
