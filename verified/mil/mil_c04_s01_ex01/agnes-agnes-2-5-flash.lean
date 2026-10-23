import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  cases hx with
  | inl hx =>
    have h₁ : x ∈ s ∩ t := hx
    have hs : x ∈ s := h₁.1
    have ht : x ∈ t := h₁.2
    have htu : x ∈ t ∪ u := Or.inl ht
    exact ⟨hs, htu⟩
  | inr hx =>
    have h₂ : x ∈ s ∩ u := hx
    have hs : x ∈ s := h₂.1
    have hu : x ∈ u := h₂.2
    have htu : x ∈ t ∪ u := Or.inr hu
    exact ⟨hs, htu⟩
