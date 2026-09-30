import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex01 {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rcases Nat.mod_two_eq_zero_or_one m with hmod | hmod
  · exact (Nat.dvd_iff_mod_eq_zero).mpr hmod
  · exfalso
    have : (m ^ 2) % 2 = 1 := by
      rw [show m ^ 2 = m * m by rw [pow_two]]
      rw [Nat.mul_mod, hmod]
    rw [Nat.dvd_iff_mod_eq_zero] at h
    omega
