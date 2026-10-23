import Mathlib

open scoped Nat
open scoped Real

/-- Find $y$: $\sqrt{19+3y} = 7$. -/
theorem mathd_algebra_263 (y : ℝ) (h₀ : 0 ≤ 19 + 3 * y) (h₁ : Real.sqrt (19 + 3 * y) = 7) :
    y = 10 := by
  have h₂ : 19 + 3 * y = 49 := by
    have := Real.sq_sqrt h₀
    rw [h₁] at this
    ring_nf at this ⊢
    linarith
  linarith
