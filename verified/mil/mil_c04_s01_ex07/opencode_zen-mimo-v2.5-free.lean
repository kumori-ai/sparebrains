import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro h
    rcases h with h | h
    · constructor
      · left
        exact h.1
      · intro h2
        exact h.2 h2.2
    · constructor
      · right
        exact h.1
      · intro h2
        exact h.2 h2.1
  · intro h
    rcases h with ⟨h1, h2⟩
    rcases h1 with h1 | h1
    · left
      constructor
      · exact h1
      · intro h3
        exact h2 ⟨h1, h3⟩
    · right
      constructor
      · exact h1
      · intro h3
        exact h2 ⟨h3, h1⟩
