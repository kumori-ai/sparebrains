import Mathlib

open scoped Nat
open scoped Real

/-- What value of $x$ will give the minimum value for $x^2- 14x + 3$? -/
theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  calc
    x ^ 2 - 14 * x + 3 = (x - 7) ^ 2 - 46 := by ring
    _ ≥ -46 := by
      have h : (x - 7) ^ 2 ≥ 0 := by
        apply pow_two_nonneg
      linarith
    _ = 7 ^ 2 - 14 * 7 + 3 := by ring
