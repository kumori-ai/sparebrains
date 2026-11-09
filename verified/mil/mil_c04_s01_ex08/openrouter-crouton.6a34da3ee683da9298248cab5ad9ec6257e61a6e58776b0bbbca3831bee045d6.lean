import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex08 : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n hn
  obtain ⟨hprime, hgt⟩ := hn
  have hprime' : Nat.Prime n := hprime
  have hgt' : n > 2 := hgt
  show ¬ Even n
  intro heven
  have h2dvd : 2 ∣ n := heven.two_dvd
  rcases hprime'.eq_one_or_self_of_dvd 2 h2dvd with h | h
  · norm_num at h
  · omega
