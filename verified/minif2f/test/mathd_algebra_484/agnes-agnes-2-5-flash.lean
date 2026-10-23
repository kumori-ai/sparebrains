import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\log_327$. -/
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have h1 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num]
    rw [Real.log_pow]
    <;> norm_num
  rw [h1]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one]
  <;> norm_num
  <;> linarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
