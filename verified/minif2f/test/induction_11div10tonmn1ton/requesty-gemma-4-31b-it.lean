import Mathlib

open scoped Nat
open scoped Real

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  induction n with
  | zero => 
    norm_num
  | succ n ih =>
    have h : 10^(n+1) - (-1 : ℤ)^(n+1) = 11 * 10^n - (10^n - (-1 : ℤ)^n) := by
      rw [pow_succ, pow_succ]
      ring
    rw [h]
    apply dvd_sub
    · apply dvd_mul_right
    · exact ih
