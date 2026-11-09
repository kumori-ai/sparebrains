import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex11 {α I : Type*} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [Set.mem_union, Set.mem_iInter]
  constructor
  · intro h
    rcases h with hs | hA
    · intro i
      exact Or.inr hs
    · intro i
      exact Or.inl (hA i)
  · intro h
    by_cases hs : x ∈ s
    · exact Or.inl hs
    · refine Or.inr ?_
      intro i
      rcases h i with hi | hs'
      · exact hi
      · exact absurd hs' hs
