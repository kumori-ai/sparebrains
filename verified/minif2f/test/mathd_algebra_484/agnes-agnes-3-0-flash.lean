import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\log_327$. -/
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have h : Real.log 27 = Real.log (3^3) := by
    norm_num
  rw [h]
  rw [Real.log_pow]
    <;>
  norm_num
  <;>
  rw [div_eq_iff]
    <;>
  norm_num
  <;>
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
