import Mathlib

open scoped Nat
open scoped Real

/-- Expand the product $(x+1)^2 \cdot x$. -/
theorem mathd_algebra_176 (x : ℝ) : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by
  simp [pow_add, add_comm, mul_comm, pow_mul, pow_add, pow_add, pow_add]
  ring
