import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  simp [Set.mem_diff, Set.mem_union, Set.mem_inter]
  tauto
