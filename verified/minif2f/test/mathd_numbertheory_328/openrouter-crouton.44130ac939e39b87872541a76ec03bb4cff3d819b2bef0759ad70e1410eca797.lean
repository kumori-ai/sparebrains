import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when 5 to the 999,999th power is divided by 7? -/
theorem mathd_numbertheory_328 : 5 ^ 999999 % 7 = 6 := by
  have h6 : 5 ^ 6 ≡ 1 [MOD 7] := by decide
  have h3 : 5 ^ 3 ≡ 6 [MOD 7] := by decide
  have h : 5 ^ 999999 ≡ 6 [MOD 7] := by
    have eq1 : 5 ^ 999999 = (5 ^ 6) ^ 166666 * 5 ^ 3 := by
      rw [show 999999 = 6 * 166666 + 3 by norm_num, pow_add, pow_mul]
    rw [eq1]
    have h' : (5 ^ 6) ^ 166666 * 5 ^ 3 ≡ 1 ^ 166666 * 6 [MOD 7] :=
      (h6.pow 166666).mul h3
    simpa using h'
  have h2 : 5 ^ 999999 % 7 = 6 % 7 := h
  exact h2
