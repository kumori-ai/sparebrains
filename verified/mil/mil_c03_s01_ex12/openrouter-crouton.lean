import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex12 {α : Type*} (r s t : Set α) : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro h1 h2 x hx
  exact h2 (h1 hx)
