import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex06 {α : Type*} (s t : Set α) : s \ t ∪ t = s ∪ t := by
  ext x
  simp only [Set.mem_union, Set.mem_sdiff, iff_true, iff_false]
  by_cases hx : x ∈ s
  · by_cases htx : x ∈ t
    · simp [hx, htx]
    · simp [hx, htx]
  · simp [hx]
