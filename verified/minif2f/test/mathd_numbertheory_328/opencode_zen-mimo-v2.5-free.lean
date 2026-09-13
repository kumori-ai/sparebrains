import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when 5 to the 999,999th power is divided by 7? -/
theorem mathd_numbertheory_328 : 5 ^ 999999 % 7 = 6 := by
  have h5_6 : 5 ^ 6 % 7 = 1 := by norm_num
  have h999 : 999999 = 6 * 166666 + 3 := by norm_num
  have h5_3 : 5 ^ 3 % 7 = 6 := by norm_num
  rw [h999]
  simp only [pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, Nat.pow_mod, h5_6, h5_3]
  norm_num
