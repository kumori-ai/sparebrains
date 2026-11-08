import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex05 {α : Type*} (s t : Set α) : s ∪ s ∩ t = s := by
  ext x
  simp only [mem_union, mem_inter_iff]
  tauto
