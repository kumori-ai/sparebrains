import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex11 {α I : Type*} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro (hs | hA)
    · intro i
      exact Or.inr hs
    · intro i
      exact Or.inl (hA i)
  · intro h
    by_cases hx : x ∈ s
    · exact Or.inl hx
    · exact Or.inr fun i => by
        have hxi : x ∈ A i ∪ s := h i
        have hxA : x ∈ A i := by
          cases' hxi with hA hS
          · exact hA
          · contradiction
        exact hxA
