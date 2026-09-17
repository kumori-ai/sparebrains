import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex01 {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  have h2 : m % 2 = 0 := by
    have h3 : (m ^ 2) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    have h4 : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
    rcases h4 with h4 | h4
    · exact h4
    · have h5 : (m ^ 2) % 2 = 1 := by
        simp [h4, pow_two, Nat.mul_mod]
      omega
  exact Nat.dvd_of_mod_eq_zero h2
