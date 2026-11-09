import Mathlib

open scoped Nat
open scoped Real

/-- Compute $29^{13} - 5^{13}$ modulo 7. -/
theorem mathd_numbertheory_728 : (29 ^ 13 - 5 ^ 13) % 7 = 3 := by
  have hle : 5 ^ 13 ≤ 29 ^ 13 := by norm_num
  have h : ((29 ^ 13 - 5 ^ 13 : ℕ) : ZMod 7) = 3 := by
    rw [Nat.cast_sub hle]
    push_cast
    decide
  have h2 : (29 ^ 13 - 5 ^ 13) ≡ 3 [MOD 7] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  simpa [Nat.ModEq] using h2
