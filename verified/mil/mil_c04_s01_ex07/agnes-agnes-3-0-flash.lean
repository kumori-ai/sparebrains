import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext a
  constructor
  · intro h
    cases h with
    | inl h =>
      have h1 : a ∈ s := h.1
      have h2 : a ∉ t := h.2
      have h3 : a ∈ s ∪ t := Or.inl h1
      have h4 : a ∉ s ∩ t := by
        intro h5
        exact h2 h5.2
      exact ⟨h3, h4⟩
    | inr h =>
      have h1 : a ∈ t := h.1
      have h2 : a ∉ s := h.2
      have h3 : a ∈ s ∪ t := Or.inr h1
      have h4 : a ∉ s ∩ t := by
        intro h5
        exact h2 h5.1
      exact ⟨h3, h4⟩
  · intro h
    have h1 : a ∈ s ∪ t := h.1
    have h2 : a ∉ s ∩ t := h.2
    cases h1 with
    | inl h1s =>
      have h4 : a ∉ t := by
        intro h4t
        have h5 : a ∈ s ∩ t := ⟨h1s, h4t⟩
        contradiction
      exact Or.inl ⟨h1s, h4⟩
    | inr h1t =>
      have h3 : a ∉ s := by
        intro h3s
        have h4 : a ∈ s ∩ t := ⟨h3s, h1t⟩
        contradiction
      exact Or.inr ⟨h1t, h3⟩
