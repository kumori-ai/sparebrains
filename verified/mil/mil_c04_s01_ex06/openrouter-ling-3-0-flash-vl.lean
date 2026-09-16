import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex06 {α : Type*} (s t : Set α) : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  · intro h
    cases' h with h1 h2
    · left; exact h1.1
    · right; exact h2
  · intro h
    cases' h with h1 h2
    · by_cases ht : x ∈ t
      · right; exact ht
      · left; exact ⟨h1, ht⟩
    · right; exact h2
