import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex11 {α I : Type*} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · intro h
    rcases h with hx | hx
    · exact fun _ => Or.inr hx
    · exact fun i => Or.inl (hx i)
  · intro h
    by_cases hs : x ∈ s
    · exact Or.inl hs
    · exact Or.inr fun i => (h i).resolve_right hs
