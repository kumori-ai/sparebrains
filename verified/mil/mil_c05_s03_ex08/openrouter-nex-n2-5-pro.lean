import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex08 {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  have hp : p = 1 ∨ p = q := Nat.Prime.eq_one_or_self_of_dvd prime_q p h
  cases hp with
  | inl hp1 =>
      exact False.elim (prime_p.ne_one hp1)
  | inr hpq =>
      exact hpq
