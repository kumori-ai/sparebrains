import Mathlib

open scoped Nat
open scoped Real

/-- Determine the remainder of 54 (mod 6). -/
theorem mathd_numbertheory_342 : 54 % 6 = 0 := by
  rw [Nat.mod_eq_zero_of_dvd]
  norm_num
