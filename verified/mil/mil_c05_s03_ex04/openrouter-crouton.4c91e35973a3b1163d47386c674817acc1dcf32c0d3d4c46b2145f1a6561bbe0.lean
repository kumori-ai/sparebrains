import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex04 {α : Type*} [DecidableEq α] (r s t : Finset α) : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨h1, h2⟩
    cases h1 with
    | inl hr => exact Or.inl hr
    | inr hs =>
      cases h2 with
      | inl hr => exact Or.inl hr
      | inr ht => exact Or.inr ⟨hs, ht⟩
  · rintro (hr | ⟨hs, ht⟩)
    · exact ⟨Or.inl hr, Or.inl hr⟩
    · exact ⟨Or.inr hs, Or.inr ht⟩
