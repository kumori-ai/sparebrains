import Mathlib

open scoped Nat
open scoped Real

/-- Find the modulo 4 residue of $121 \cdot 122 \cdot 123$. -/
theorem mathd_numbertheory_517 : 121 * 122 * 123 % 4 = 2 := by
  norm_num
