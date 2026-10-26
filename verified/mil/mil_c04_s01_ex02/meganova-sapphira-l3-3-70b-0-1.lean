import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intros x hx
  have h1 : x ∈ s := hx.1
  have h2 : x ∉ t ∪ u := hx.2
  have h3 : x ∉ t := mt (λ h => Or.inl h) h2
  have h4 : x ∉ u := mt (λ h => Or.inr h) h2
  exact ⟨⟨h1, h3⟩, h4⟩
