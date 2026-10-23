import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x
  intro h
  cases h with
  | inl h1 => 
    have h2 : x ∈ s := by
      apply h1.1
    have h3 : x ∈ t := by
      apply h1.2
    have h4 : x ∈ t ∪ u := by
      apply Or.inl h3
    have h5 : x ∈ s ∩ (t ∪ u) := by
      constructor
      · exact h2
      · exact h4
    exact h5
  | inr h1 => 
    have h2 : x ∈ s := by
      apply h1.1
    have h3 : x ∈ u := by
      apply h1.2
    have h4 : x ∈ t ∪ u := by
      apply Or.inr h3
    have h5 : x ∈ s ∩ (t ∪ u) := by
      constructor
      · exact h2
      · exact h4
    exact h5
