import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when $5^{30}$ is divided by 7? -/
theorem mathd_numbertheory_229 : 5 ^ 30 % 7 = 1 := by
  have h6 : 5 ^ 6 % 7 = 1 := by norm_num
  have h1mod : (1 : ℕ) % 7 = 1 := by norm_num
  have h6_mod : 5 ^ 6 ≡ 1 [MOD 7] := by
    rw [Nat.ModEq, h6, h1mod]
  have h30_mod : 5 ^ 30 ≡ 1 [MOD 7] := by
    calc
      5 ^ 30 = (5 ^ 6) ^ 5 := by norm_num
      _ ≡ 1 ^ 5 [MOD 7] := h6_mod.pow 5
      _ = 1 := by norm_num
      _ ≡ 1 [MOD 7] := by rfl
  rw [Nat.ModEq] at h30_mod
  rw [h30_mod, h1mod]
