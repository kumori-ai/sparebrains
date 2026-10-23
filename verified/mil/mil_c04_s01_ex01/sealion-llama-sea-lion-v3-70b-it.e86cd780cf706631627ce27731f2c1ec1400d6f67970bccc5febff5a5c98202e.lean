import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x
  intro hx
  cases hx with
  | inl hx =>
    have h1 : x ∈ s := hx.1
    have h2 : x ∈ t := hx.2
    have h3 : x ∈ t ∪ u := Or.inl h2
    exact ⟨h1, h3⟩
  | inr hx =>
    have h1 : x ∈ s := hx.1
    have h2 : x ∈ u := hx.2
    have h3 : x ∈ t ∪ u := Or.inr h2
    exact ⟨h1, h3⟩
