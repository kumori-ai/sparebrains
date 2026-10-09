import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex02 {α β : Type*} (f : α → β) (s : Set α) (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x hx
  rw [Set.mem_preimage] at hx
  rw [Set.mem_image] at hx
  obtain ⟨y, ys, hy⟩ := hx
  have : y = x := h hy
  rw [this] at ys
  exact ys
