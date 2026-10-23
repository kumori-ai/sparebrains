import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex06 {α β : Type*} (f : α → β) (u v : Set β) (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x hx
  exact h hx
