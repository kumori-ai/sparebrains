import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 13. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex13 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  have h₁ : (m % 4) * (n % 4) % 4 = 3 := by
    rw [← h]
    rw [Nat.mul_mod m n 4]
  have h₂ : m % 4 < 4 := Nat.mod_lt m (by decide)
  have h₃ : n % 4 < 4 := Nat.mod_lt n (by decide)
  interval_cases m % 4 <;> interval_cases n % 4 <;> simp_all
