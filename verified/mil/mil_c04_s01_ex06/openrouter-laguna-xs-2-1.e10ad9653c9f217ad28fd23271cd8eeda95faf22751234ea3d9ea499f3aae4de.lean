import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex06 {α : Type*} (s t : Set α) : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h.1
    · exact Or.inr h
  · intro h
    rcases h with h | h
    · by_cases hxt : x ∈ t
      · exact Or.inr hxt
      · exact Or.inl ⟨h, hxt⟩
    · exact Or.inr h
