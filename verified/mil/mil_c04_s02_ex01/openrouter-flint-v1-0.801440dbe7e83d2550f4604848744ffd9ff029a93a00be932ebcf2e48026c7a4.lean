import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex01 {α β : Type*} (f : α → β) (s : Set α) (v : Set β) : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x hx
    have hmem : f x ∈ f '' s := (Set.mem_image f s (f x)).mpr ⟨x, hx, rfl⟩
    exact h hmem
  · intro h
    intro y hy
    have hmem : ∃ x, x ∈ s ∧ f x = y := (Set.mem_image f s y).mp hy
    rcases hmem with ⟨x, hx, hxy⟩
    rw [← hxy]
    exact h hx
