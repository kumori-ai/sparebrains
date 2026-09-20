import Mathlib

open scoped Nat
open scoped Real

/-- Given $f(x)=cx^3-9x+3$ and $f(2)=9$, find the value of $c$. -/
theorem mathd_algebra_148 (c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = c * x ^ 3 - 9 * x + 3)
    (h₁ : f 2 = 9) : c = 3 := by
  have h_eq : f 2 = c * 2 ^ 3 - 9 * 2 + 3 := h₀ 2
  rw [h_eq] at h₁
  norm_num at h₁
  -- h₁ is now: c * 8 - 18 + 3 = 9
  -- c * 8 - 15 = 9
  -- c * 8 = 24
  -- c = 3
  linarith
