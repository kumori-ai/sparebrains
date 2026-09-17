import Mathlib

open scoped Nat
open scoped Real

/--
A $3491$ by $3491$ square has its length decreased by $60$ and its width increased by $60$.  By how much does its area change? -/
theorem mathd_algebra_296 : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by
  have h : (3491 - 60) * (3491 + 60) - 3491 ^ 2 = -3600 := by ring
  rw [h]
  norm_num
