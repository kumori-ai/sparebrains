import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  cases hx with
  | inl hst =>
    cases hst with
    | intro hs ht =>
      constructor
      · exact hs
      · left
        exact ht
  | inr hsu =>
    cases hsu with
    | intro hs hu =>
      constructor
      · exact hs
      · right
        exact hu
