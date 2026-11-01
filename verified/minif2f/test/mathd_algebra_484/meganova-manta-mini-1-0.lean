import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\log_327$. -/
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have h : Real.log 27 = Real.log (3 ^ 3) := by norm_num
  rw [h, Real.log_pow, Nat.cast_ofNat]
  field_simp
