import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  have hnt : x ∉ t := by
    intro ht
    apply hx.2
    left
    exact ht
  have hnu : x ∉ u := by
    intro hu
    apply hx.2
    right
    exact hu
  constructor
  · constructor
    · exact hx.1
    · exact hnt
  · exact hnu
