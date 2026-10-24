import Mathlib

open scoped Nat
open scoped Real

/-- Given $f(x)=cx^3-9x+3$ and $f(2)=9$, find the value of $c$. -/
theorem mathd_algebra_148 (c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = c * x ^ 3 - 9 * x + 3)
    (h₁ : f 2 = 9) : c = 3 := by
  have h₂ : c * 2 ^ 3 - 9 * 2 + 3 = 9 := by
    simpa [h₀] using h₁
  have h₃ : c * 8 - 18 + 3 = 9 := by norm_num at h₂ ⊢; simpa using h₂
  have h₄ : c * 8 - 15 = 9 := by norm_num at h₃ ⊢; linarith
  have h₅ : c * 8 = 24 := by linarith
  have h₆ : c = 3 := by
    apply mul_left_cancel₀ (show (8 : ℝ) ≠ 0 by norm_num)
    linarith
  exact h₆
