import Mathlib

open scoped Nat
open scoped Real

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have h : (11 : ℤ) ∣ 10 * (10 ^ n - (-1 : ℤ) ^ n) :=
        dvd_mul_of_dvd_right ih 10
      have h2 : (11 : ℤ) ∣ 11 * (-1 : ℤ) ^ n :=
        dvd_mul_right (11 : ℤ) ((-1 : ℤ) ^ n)
      have h_eq : (10 : ℤ) ^ (n + 1) - (-1 : ℤ) ^ (n + 1) =
          10 * (10 ^ n - (-1 : ℤ) ^ n) + 11 * (-1 : ℤ) ^ n := by
        rw [pow_succ, pow_succ]
        ring
      rw [h_eq]
      exact dvd_add h h2
