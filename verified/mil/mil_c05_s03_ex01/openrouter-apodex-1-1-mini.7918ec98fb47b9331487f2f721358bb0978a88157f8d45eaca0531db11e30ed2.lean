import Mathlib

open BigOperators

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex01 {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  have : m < 2 := Nat.not_le.mp h
  have : m = 0 ∨ m = 1 := by omega
  cases this with
  | inl h2 => exact h0 h2
  | inr h2 => exact h1 h2
