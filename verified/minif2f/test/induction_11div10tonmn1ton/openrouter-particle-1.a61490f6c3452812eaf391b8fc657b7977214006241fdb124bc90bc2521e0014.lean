import Mathlib

open scoped Nat
open scoped Real

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h : 10 ^ (n + 1) - (-1 : ℤ) ^ (n + 1) =
          10 * (10 ^ n - (-1 : ℤ) ^ n) + 11 * (-1 : ℤ) ^ n := by
        rw [pow_succ, pow_succ]
        ring
      rw [h]
      apply dvd_add
      · rcases ih with ⟨k, hk⟩
        use 10 * k
        rw [hk]
        ring
      · exact ⟨(-1 : ℤ) ^ n, by ring⟩
