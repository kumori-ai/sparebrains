import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex08 {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  exact (Nat.prime_dvd_prime_iff_eq prime_p prime_q).mp h
