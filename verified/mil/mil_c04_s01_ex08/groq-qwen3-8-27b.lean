import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex08 : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n hn
  rcases hn with ⟨hprime, hgt⟩
  rcases Nat.Prime.eq_two_or_odd hprime with (rfl | hodd)
  · exact False.elim (Nat.lt_irrefl 2 hgt)
  · intro heven
    rw [Nat.even_iff] at heven
    omega
