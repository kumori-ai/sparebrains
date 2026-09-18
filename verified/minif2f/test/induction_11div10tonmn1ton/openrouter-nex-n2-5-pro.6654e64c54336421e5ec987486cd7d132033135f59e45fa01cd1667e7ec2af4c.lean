import Mathlib

open scoped Nat
open scoped Real

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [show (10 : ℤ) ^ n.succ - (-1 : ℤ) ^ n.succ =
            10 * (10 ^ n - (-1 : ℤ) ^ n) + 11 * (-1 : ℤ) ^ n by
          simp only [pow_succ]
          ring]
    exact dvd_add (dvd_mul_of_dvd_right ih 10) (dvd_mul_right 11 _)
