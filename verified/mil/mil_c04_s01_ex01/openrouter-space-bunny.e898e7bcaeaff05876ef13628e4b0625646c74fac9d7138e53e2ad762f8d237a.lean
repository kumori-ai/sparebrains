import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  constructor
  · exact hx.elim (fun h => h.1) (fun h => h.1)
  · rcases hx with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
