import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex05 {α β : Type*} (f : α → β) (s t : Set α) (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩
