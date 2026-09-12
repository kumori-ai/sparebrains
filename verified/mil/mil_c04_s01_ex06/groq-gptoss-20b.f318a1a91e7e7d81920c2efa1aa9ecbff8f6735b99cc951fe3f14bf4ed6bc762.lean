import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex06 {α : Type*} (s t : Set α) : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨hx_s, hx_not_t⟩
      exact Or.inl hx_s
    · exact Or.inr hx
  · intro hx
    rcases hx with hx | hx
    · by_cases hxt : x ∈ t
      · exact Or.inr hxt
      · exact Or.inl ⟨hx, hxt⟩
    · exact Or.inr hx
