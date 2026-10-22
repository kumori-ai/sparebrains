import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  rcases hx with ⟨hs, ht⟩ | ⟨hs, hu⟩
  · exact ⟨hs, Or.inl ht⟩
  · exact ⟨hs, Or.inr hu⟩
