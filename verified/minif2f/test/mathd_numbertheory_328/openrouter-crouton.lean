import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when 5 to the 999,999th power is divided by 7? -/
theorem mathd_numbertheory_328 : 5 ^ 999999 % 7 = 6 := by
  have h_eq : (5 ^ 6) ^ 166666 * 5 ^ 3 = 5 ^ 999999 := by
    rw [← pow_mul, ← pow_add]
  rw [← h_eq, Nat.mul_mod, Nat.pow_mod, Nat.pow_mod]
  norm_num
