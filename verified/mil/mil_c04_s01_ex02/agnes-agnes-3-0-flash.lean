import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  have h1 : x ∈ s := hx.1
  have h2 : x ∉ t ∪ u := hx.2
  have h3 : x ∉ t := by
    intro ht
    have htu : x ∈ t ∪ u := Or.inl ht
    exact h2 htu
  have h4 : x ∉ u := by
    intro hu
    have htu : x ∈ t ∪ u := Or.inr hu
    exact h2 htu
  constructor
  · constructor
    · exact h1
    · exact h3
  · exact h4
