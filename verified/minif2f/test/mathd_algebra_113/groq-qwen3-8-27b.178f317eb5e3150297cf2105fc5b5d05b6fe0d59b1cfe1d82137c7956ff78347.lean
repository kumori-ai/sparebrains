import Mathlib

open scoped Nat
open scoped Real

/-- What value of $x$ will give the minimum value for $x^2- 14x + 3$? -/
theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  have h : (x - 7) ^ 2 ≥ 0 := sq_nonneg (x - 7)
  have h2 : x ^ 2 - 14 * x + 3 = (x - 7) ^ 2 - 46 := by ring
  have h3 : (7 : ℝ) ^ 2 - 14 * 7 + 3 = -46 := by norm_num
  rw [h2, h3]
  linarith
