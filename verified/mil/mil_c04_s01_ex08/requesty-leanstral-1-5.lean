import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex08 : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n hn
  rcases hn with ⟨hn_prime, hn_gt⟩
  intro h_even
  have hn_eq_2 : n = 2 := (hn_prime.even_iff.mp h_even)
  rw [hn_eq_2] at hn_gt
  exact Nat.lt_irrefl _ hn_gt
