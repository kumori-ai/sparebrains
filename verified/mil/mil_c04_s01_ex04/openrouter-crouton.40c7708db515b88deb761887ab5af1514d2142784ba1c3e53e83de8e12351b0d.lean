import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex04 {α : Type*} (s t : Set α) : s ∩ (s ∪ t) = s := by
  exact inter_eq_self_of_subset_left subset_union_left
