import Mathlib

open scoped Nat
open scoped Real

/-- Compute $91^2$ in your head. -/
theorem mathd_algebra_304 : 91 ^ 2 = 8281 := by
  -- Compute 91² using the formula (a + b)² = a² + 2ab + b² where a = 90 and b = 1
  -- 90² = 8100
  -- 2 * 90 * 1 = 180
  -- 1² = 1
  -- Sum: 8100 + 180 + 1 = 8281
  rfl
