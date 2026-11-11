import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex11 {α I : Type*} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  classical
  ext x
  by_cases h : x ∈ s
  · simp [h, Set.mem_union, Set.mem_iInter]
  · simp [h, Set.mem_union, Set.mem_iInter]
