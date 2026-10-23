import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  cases hx with
  | inl h =>
    have h1 : x ∈ s ∧ x ∈ t := h
    exact ⟨h1.1, Or.inl h1.2⟩
  | inr h =>
    have h2 : x ∈ s ∧ x ∈ u := h
    exact ⟨h2.1, Or.inr h2.2⟩
