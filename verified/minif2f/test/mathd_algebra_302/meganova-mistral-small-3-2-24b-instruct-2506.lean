import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\left(\frac{i}{2}\right)^2$. -/
theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by
  have : (Complex.I / 2) ^ 2 = (Complex.I * Complex.I) / (2 * 2) := by ring
  rw [this, Complex.I_mul_I]
  ring
