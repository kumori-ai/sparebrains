import Mathlib

open scoped Nat
open scoped Real

/-- Compute $91^2$ in your head. -/
theorem mathd_algebra_304 : 91 ^ 2 = 8281 := by
  simp [pow_two, mul_assoc, mul_comm 91 2, mul_one]
