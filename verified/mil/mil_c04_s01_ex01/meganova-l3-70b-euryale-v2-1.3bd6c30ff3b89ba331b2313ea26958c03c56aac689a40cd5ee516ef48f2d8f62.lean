import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intros x hx
  cases hx
  case inl h =>
    have hst : x ∈ s := h.left
    have ht : x ∈ t := h.right
    have htu : x ∈ t ∪ u := Or.inl ht
    exact ⟨hst, htu⟩
  case inr h =>
    have hsu : x ∈ s := h.left
    have hu : x ∈ u := h.right
    have htu : x ∈ t ∪ u := Or.inr hu
    exact ⟨hsu, htu⟩
