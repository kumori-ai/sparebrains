import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\log_327$. -/
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have h : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow, mul_div_cancel_right₀ _ h]
  norm_num
