import Mathlib

open scoped Nat
open scoped Real

/-- Expand $(x+3)(2x-6)$. -/
theorem mathd_algebra_432 (x : ℝ) : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := by
  ring
