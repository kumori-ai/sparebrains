import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when 5 to the 999,999th power is divided by 7? -/
theorem mathd_numbertheory_328 : 5 ^ 999999 % 7 = 6 := by
  have h : 5 ^ 6 % 7 = 1 := by norm_num
  have : 5 ^ 999999 % 7 = (5 ^ 3) % 7 := by
    have h₁ : 999999 = 6 * 166666 + 3 := by norm_num
    rw [h₁]
    rw [pow_add, pow_mul]
    simp [h, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod, Nat.add_mod]
    <;> norm_num
  norm_num at this
  exact this
