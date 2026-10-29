import Mathlib

open scoped Nat
open scoped Real

/-- Solve  \[\frac{x-9}{x+1}=2\]for $x$. -/
theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by
  have h₂ : x + 1 ≠ 0 := by
    intro h
    apply h₀
    linarith
  field_simp [h₂] at h₁
  linarith
