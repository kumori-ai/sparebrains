import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\log_327$. -/
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have hlog : Real.log 3 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  apply (div_eq_iff hlog).2
  rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
  ring
