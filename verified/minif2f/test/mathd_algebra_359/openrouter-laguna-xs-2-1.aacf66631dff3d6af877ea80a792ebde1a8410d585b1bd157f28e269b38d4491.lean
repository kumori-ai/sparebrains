import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $y$ in the arithmetic sequence $y + 6$, $12$, $y$? -/
theorem mathd_algebra_359 (y : ℝ) (h₀ : y + 6 + y = 2 * 12) : y = 9 := by
  linarith [h₀]
