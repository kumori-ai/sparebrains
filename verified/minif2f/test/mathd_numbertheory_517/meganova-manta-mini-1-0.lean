import Mathlib

open scoped Nat
open scoped Real

/-- Find the modulo 4 residue of $121 \cdot 122 \cdot 123$. -/
theorem mathd_numbertheory_517 : 121 * 122 * 123 % 4 = 2 := by
  calc
  121 * 122 * 123 % 4 = (3 * 2 * 3) % 4
    := by simp [mul_assoc, mul_comm 3 2, mul_comm 3 3]
  _ = 3 * 2 % 4
    := by simp [mul_assoc, mul_comm 3 2]
  _ = 6 % 4
    := by ring
  _ = 2
    := by norm_num
