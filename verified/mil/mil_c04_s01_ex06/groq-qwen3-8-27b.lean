import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex06 {α : Type*} (s t : Set α) : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  · intro h
    cases h with
    | inl h =>
      exact Or.inl h.1
    | inr h =>
      exact Or.inr h
  · intro h
    cases h with
    | inl h =>
      by_cases ht : x ∈ t
      · exact Or.inr ht
      · exact Or.inl ⟨h, ht⟩
    | inr h =>
      exact Or.inr h
