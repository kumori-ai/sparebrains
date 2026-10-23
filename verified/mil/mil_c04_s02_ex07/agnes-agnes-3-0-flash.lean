import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex07 {α β : Type*} (f : α → β) (u v : Set β) : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · intro h
    simp only [Set.mem_preimage, Set.mem_union] at h
    exact Or.elim h (fun h' => Or.inl h') (fun h' => Or.inr h')
  · intro h
    simp only [Set.mem_preimage, Set.mem_union]
    cases h with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr h
