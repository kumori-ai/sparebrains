import Mathlib

open scoped Nat
open scoped Real

/-- Solve  \[\frac{x-9}{x+1}=2\]for $x$. -/
theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by
  have hden : x + 1 ≠ 0 := by
    intro h
    have : x = -1 := by linarith
    exact h₀ this
  field_simp [hden] at h₁
  linarith
