import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex11 {α I : Type*} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  classical
  ext x
  simp only [Set.mem_union, Set.mem_iInter]
  constructor
  · rintro (hs | hA)
    · intro i
      exact Or.inr hs
    · intro i
      exact Or.inl (hA i)
  · intro h
    by_cases hs : x ∈ s
    · exact Or.inl hs
    · right
      intro i
      rcases h i with hAi | hsi
      · exact hAi
      · exact (hs hsi).elim
