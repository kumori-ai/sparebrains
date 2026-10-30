import Mathlib

open scoped Nat
open scoped Real

/-- Find $y$: $\sqrt{19+3y} = 7$. -/
theorem mathd_algebra_263 (y : ℝ) (h₀ : 0 ≤ 19 + 3 * y) (h₁ : Real.sqrt (19 + 3 * y) = 7) :
    y = 10 := by
  have h_sq := congrArg (fun x => x ^ 2) h₁
  rw [Real.sq_sqrt h₀] at h_sq
  rw [pow_two] at h_sq
  ring_nf at h_sq
  linarith
