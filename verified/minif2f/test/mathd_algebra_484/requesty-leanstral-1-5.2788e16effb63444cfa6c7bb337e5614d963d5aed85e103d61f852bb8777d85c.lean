import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\log_327$. -/
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have hlog : Real.log 27 = 3 * Real.log 3 := by
    calc
      Real.log 27 = Real.log ((3:ℝ)^3) := by norm_num
      _ = 3 * Real.log 3 := by rw [Real.log_pow, Nat.cast_ofNat]
  have h : Real.log 3 ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  rw [hlog]
  field_simp [h]
