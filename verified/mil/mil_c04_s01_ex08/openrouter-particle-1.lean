import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex08 : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  rintro n ⟨hp, hn⟩ he
  have h2dvd : 2 ∣ n := even_iff_two_dvd.mp he
  rcases hp.eq_one_or_self_of_dvd 2 h2dvd with h | h
  · exact (by norm_num : (2 : Nat) ≠ 1) h
  · exact Nat.lt_irrefl 2 (h.symm ▸ hn)
