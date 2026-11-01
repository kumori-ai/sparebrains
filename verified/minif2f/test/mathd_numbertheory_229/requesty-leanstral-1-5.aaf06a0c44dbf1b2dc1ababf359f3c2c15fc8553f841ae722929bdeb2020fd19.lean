import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when $5^{30}$ is divided by 7? -/
theorem mathd_numbertheory_229 : 5 ^ 30 % 7 = 1 := by
  have h5_2 : 5 ^ 2 ≡ 4 [MOD 7] := by norm_num
  have h5_3 : 5 ^ 3 ≡ 6 [MOD 7] := by
    calc
      5 ^ 3 = 5 * 5 ^ 2 := by ring
      _ ≡ 5 * 4 [MOD 7] := (Nat.ModEq.refl 5).mul h5_2
      _ = 20 := by norm_num
      _ ≡ 6 [MOD 7] := by norm_num
  have h5_6 : 5 ^ 6 ≡ 1 [MOD 7] := by
    calc
      5 ^ 6 = (5 ^ 3) ^ 2 := by ring
      _ ≡ 6 ^ 2 [MOD 7] := h5_3.pow 2
      _ = 36 := by norm_num
      _ ≡ 1 [MOD 7] := by norm_num
  have h5_30 : 5 ^ 30 ≡ 1 [MOD 7] := by
    calc
      5 ^ 30 = (5 ^ 6) ^ 5 := by ring
      _ ≡ 1 ^ 5 [MOD 7] := h5_6.pow 5
      _ = 1 := by norm_num
  simpa [Nat.mod_eq_of_lt (by norm_num : 1 < 7)] using h5_30
