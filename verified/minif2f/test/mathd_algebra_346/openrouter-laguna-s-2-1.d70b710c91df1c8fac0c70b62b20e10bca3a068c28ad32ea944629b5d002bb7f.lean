import Mathlib

open scoped Nat
open scoped Real

/-- Let $f(x) = 2x-3$ and $g(x) = x+1$. What is the value of $g(f(5)-1)$? -/
theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
  have h₂ : f 5 = 2 * 5 - 3 := by
    exact h₀ 5
  have h₃ : f 5 = 7 := by
    norm_num at h₂
    exact h₂
  have h₄ : f 5 - 1 = 6 := by
    rw [h₃]
    norm_num
  have h₅ : g (f 5 - 1) = g 6 := by
    rw [h₄]
  have h₆ : g 6 = 6 + 1 := by
    exact h₁ 6
  have h₇ : g (f 5 - 1) = 6 + 1 := by
    rw [h₅, h₆]
  have h₈ : g (f 5 - 1) = 7 := by
    norm_num at h₇
    exact h₇
  exact h₈
