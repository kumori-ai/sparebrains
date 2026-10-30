import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex08 {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  have hp1 : 1 < p := Nat.Prime.one_lt prime_p
  rcases prime_q.eq_one_or_self_of_dvd p h with (h1 | h_eq)
  · exact (hp1.ne' h1).elim
  · exact h_eq
