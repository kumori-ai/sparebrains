import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex08 : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n hn
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hn
  obtain ⟨hprime, hgt⟩ := hn
  show ¬Even n
  intro heven
  rw [even_iff_two_dvd] at heven
  rcases hprime.eq_one_or_self_of_dvd 2 heven with h | h
  · norm_num at h
  · omega
