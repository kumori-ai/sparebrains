import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex04 {α : Type*} (s t : Set α) : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  · intro hx
    cases hx with
    | intro hxs hunion =>
      exact hxs
  · intro hx
    constructor
    · exact hx
    · exact Or.inl hx
