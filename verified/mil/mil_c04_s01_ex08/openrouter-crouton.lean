import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex08 : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n hn
  simp only [mem_inter_iff, mem_setOf_eq] at hn
  obtain ⟨hprime, hgt⟩ := hn
  simp only [mem_setOf_eq]
  intro heven
  obtain ⟨k, hk⟩ := heven
  have hdvd : 2 ∣ n := ⟨k, by omega⟩
  rcases hprime.eq_one_or_self_of_dvd 2 hdvd with h | h
  · exact absurd h (by norm_num)
  · omega
