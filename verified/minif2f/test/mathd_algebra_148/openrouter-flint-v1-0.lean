import Mathlib

open scoped Nat
open scoped Real

/-- Given $f(x)=cx^3-9x+3$ and $f(2)=9$, find the value of $c$. -/
theorem mathd_algebra_148 (c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = c * x ^ 3 - 9 * x + 3)
    (h₁ : f 2 = 9) : c = 3 := by
  have h₂ : c * (2:ℝ)^3 - 9 * (2:ℝ) + 3 = 9 := by
    calc
      c * (2:ℝ)^3 - 9 * (2:ℝ) + 3 = f 2 := by rw [← h₀ 2]
      _ = 9 := h₁
  ring_nf at h₂
  nlinarith
