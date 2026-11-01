import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\log_327$. -/
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have hlog3_ne_zero : Real.log (3 : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  calc
    Real.log 27 / Real.log 3 = Real.log ((3 : ℝ) ^ 3) / Real.log 3 := by norm_num
    _ = ((3 : ℕ) : ℝ) * Real.log (3 : ℝ) / Real.log 3 := by rw [Real.log_pow]
    _ = 3 := by
      field_simp [hlog3_ne_zero]
      norm_num
