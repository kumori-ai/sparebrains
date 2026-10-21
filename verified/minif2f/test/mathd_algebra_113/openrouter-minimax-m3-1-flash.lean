import Mathlib

open scoped Nat
open scoped Real

/-- What value of $x$ will give the minimum value for $x^2- 14x + 3$? -/
theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  nlinarith [sq_nonneg (x - 7)]
