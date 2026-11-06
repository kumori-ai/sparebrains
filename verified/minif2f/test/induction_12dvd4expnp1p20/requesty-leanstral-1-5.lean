import Mathlib

open scoped Nat
open scoped Real

theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  zify
  induction n with
  | zero => norm_num
  | succ k IH =>
    have h : (4 : ℤ) ^ (k + 1 + 1) + 20 = 4 * ((4 : ℤ) ^ (k + 1) + 20) - 60 := by
      rw [pow_succ, mul_comm]
      ring
    rw [h]
    have h12_60 : (12 : ℤ) ∣ (60 : ℤ) := by norm_num
    have h4 : (12 : ℤ) ∣ 4 * ((4 : ℤ) ^ (k + 1) + 20) :=
      dvd_mul_of_dvd_right IH 4
    exact dvd_sub h4 h12_60
