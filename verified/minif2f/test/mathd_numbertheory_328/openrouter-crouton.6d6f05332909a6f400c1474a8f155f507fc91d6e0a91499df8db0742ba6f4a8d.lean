import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when 5 to the 999,999th power is divided by 7? -/
theorem mathd_numbertheory_328 : 5 ^ 999999 % 7 = 6 := by
  have h1 : 5 ^ 3 ≡ 6 [MOD 7] := by decide
  have h2 : (5 ^ 3) ^ 333333 ≡ 6 ^ 333333 [MOD 7] := h1.pow 333333
  have h3 : 6 ^ 2 ≡ 1 [MOD 7] := by decide
  have h4 : (6 ^ 2) ^ 166666 ≡ 1 ^ 166666 [MOD 7] := h3.pow 166666
  have h5 : (6 ^ 2) ^ 166666 * 6 ≡ 1 ^ 166666 * 6 [MOD 7] :=
    h4.mul (Nat.ModEq.refl 6)
  have h8 : 6 ^ 333333 ≡ 6 [MOD 7] := by
    have heq : 6 ^ 333333 = (6 ^ 2) ^ 166666 * 6 := by
      rw [← pow_mul, ← pow_succ]
    rw [heq]
    simpa using h5
  have heq2 : 5 ^ 999999 = (5 ^ 3) ^ 333333 := by
    rw [← pow_mul]
  have h9 : 5 ^ 999999 ≡ 6 [MOD 7] := by
    rw [heq2]
    exact h2.trans h8
  exact h9
