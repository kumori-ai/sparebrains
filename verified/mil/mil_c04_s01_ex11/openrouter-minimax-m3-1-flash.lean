import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex11 {α I : Type*} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [Set.mem_union, Set.mem_iInter]
  constructor
  · intro hx
    rcases hx with hxs | hxA
    · intro i
      exact Or.inr hxs
    · intro i
      exact Or.inl (hxA i)
  · intro hx
    by_cases hxs : x ∈ s
    · exact Or.inl hxs
    · apply Or.inr
      intro i
      exact (hx i).resolve_right hxs
