import Mathlib

open scoped Nat
open scoped Real

/-- Find the units digit of $16^{17} \times 17^{18} \times 18^{19}$. -/
theorem mathd_numbertheory_212 : 16 ^ 17 * 17 ^ 18 * 18 ^ 19 % 10 = 8 := by
  have h16 : (16 : ℕ) ≡ 6 [MOD 10] := by
    decide
  have h17 : (17 : ℕ) ≡ 7 [MOD 10] := by
    decide
  have h18 : (18 : ℕ) ≡ 8 [MOD 10] := by
    decide
  have h6pow : (6 : ℕ) ^ 17 ≡ 6 [MOD 10] := by
    decide
  have h7pow : (7 : ℕ) ^ 18 ≡ 9 [MOD 10] := by
    decide
  have h8pow : (8 : ℕ) ^ 19 ≡ 2 [MOD 10] := by
    decide
  have h16pow : (16 : ℕ) ^ 17 ≡ 6 [MOD 10] :=
    (h16.pow 17).trans h6pow
  have h17pow : (17 : ℕ) ^ 18 ≡ 9 [MOD 10] :=
    (h17.pow 18).trans h7pow
  have h18pow : (18 : ℕ) ^ 19 ≡ 2 [MOD 10] :=
    (h18.pow 19).trans h8pow
  have hprod : (16 ^ 17 * 17 ^ 18 * 18 ^ 19) ≡ (6 * 9 * 2) [MOD 10] :=
    (h16pow.mul h17pow).mul h18pow
  have h6_9_2 : (6 * 9 * 2) % 10 = 8 := by
    decide
  calc
    (16 ^ 17 * 17 ^ 18 * 18 ^ 19) % 10 = (6 * 9 * 2) % 10 := hprod
    _ = 8 := h6_9_2
