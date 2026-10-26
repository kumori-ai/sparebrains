import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intros x hx
  cases hx
  case inl h => exact ⟨h.1, Or.inl h.2⟩
  case inr h => exact ⟨h.1, Or.inr h.2⟩
