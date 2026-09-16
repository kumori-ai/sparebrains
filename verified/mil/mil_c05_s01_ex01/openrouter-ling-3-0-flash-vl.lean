import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex01 {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  have h2 : Nat.Prime 2 := by decide
  exact Nat.Prime.dvd_of_dvd_pow h2 h
