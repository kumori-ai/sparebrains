import Mathlib

open scoped Nat
open scoped Real

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨10 * k + (-1 : ℤ) ^ n, ?_⟩
    have h : (10 : ℤ) ^ (n + 1) - (-1 : ℤ) ^ (n + 1)
        = 10 * (10 ^ n - (-1 : ℤ) ^ n) + 11 * (-1 : ℤ) ^ n := by
      rw [pow_succ, pow_succ]
      ring
    rw [h, hk]
    ring
