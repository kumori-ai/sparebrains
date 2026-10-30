import Mathlib

open scoped Nat
open scoped Real

/-- Expand the product $(x+1)^2 \cdot x$. -/
theorem mathd_algebra_176 (x : ℝ) : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by
  simp only [pow_two, pow_mul, mul_assoc, mul_comm, add_mul, pow_add]
  ring
