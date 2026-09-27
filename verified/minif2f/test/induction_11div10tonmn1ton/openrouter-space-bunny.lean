import Mathlib

open scoped Nat
open scoped Real

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨10 * k + (-1 : ℤ) ^ n, ?_⟩
      calc
        10 ^ Nat.succ n - (-1 : ℤ) ^ Nat.succ n =
            10 * (10 ^ n - (-1 : ℤ) ^ n) + 11 * (-1 : ℤ) ^ n := by
              rw [pow_succ, pow_succ]
              ring
        _ = 11 * (10 * k + (-1 : ℤ) ^ n) := by
              rw [hk]
              ring
