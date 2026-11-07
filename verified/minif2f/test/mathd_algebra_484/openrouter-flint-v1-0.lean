import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\log_327$. -/
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have h : (3 : ℝ) ^ 3 = 27 := by norm_num
  rw [← h, Real.log_pow]
  have hlog : Real.log 3 ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  field_simp [hlog]
  ring
