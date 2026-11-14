import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex01 {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two] at h
  rcases Nat.prime_two.dvd_mul.mp h with h' | h'
  · exact h'
  · exact h'
