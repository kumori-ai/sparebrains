import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex11 {α I : Type*} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro (hx | hx)
    · intro i
      exact Or.inr hx
    · intro i
      exact Or.inl (hx i)
  · intro h
    by_cases hx : x ∈ s
    · exact Or.inl hx
    · refine Or.inr fun i => ?_
      rcases h i with hi | hi
      · exact hi
      · exact absurd hi hx
