import Mathlib

open scoped Nat
open scoped Real

/-- Compute $29^{13} - 5^{13}$ modulo 7. -/
theorem mathd_numbertheory_728 : (29 ^ 13 - 5 ^ 13) % 7 = 3 := by
  norm_num
