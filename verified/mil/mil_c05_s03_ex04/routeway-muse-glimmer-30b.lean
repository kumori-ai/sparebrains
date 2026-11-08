import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex04 {α : Type*} [DecidableEq α] (r s t : Finset α) : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    cases h1 with
    | inl hr => left; exact hr
    | inr hs =>
      cases h2 with
      | inl hr => left; exact hr
      | inr ht => right; exact ⟨hs, ht⟩
  · intro h
    cases h with
    | inl hr => exact ⟨Or.inl hr, Or.inl hr⟩
    | inr hst => exact ⟨Or.inr hst.1, Or.inr hst.2⟩
