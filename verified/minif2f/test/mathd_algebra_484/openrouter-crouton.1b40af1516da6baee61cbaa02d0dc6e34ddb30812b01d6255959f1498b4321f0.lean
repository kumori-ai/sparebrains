import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\log_327$. -/
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have hpos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h27 : Real.log 27 = 3 * Real.log 3 := by
    have h27eq : (27 : ℝ) = 3 ^ 3 := by norm_num
    rw [h27eq, Real.log_pow]
    push_cast
    ring
  rw [h27]
  field_simp
