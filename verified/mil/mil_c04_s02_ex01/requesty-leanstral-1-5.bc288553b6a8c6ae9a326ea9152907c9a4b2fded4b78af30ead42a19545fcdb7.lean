import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex01 {α β : Type*} (f : α → β) (s : Set α) (v : Set β) : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x hx
    have hfx : f x ∈ f '' s := Set.mem_image_of_mem f hx
    have hfxv : f x ∈ v := h hfx
    exact hfxv
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx' : x ∈ f ⁻¹' v := h hx
    exact hx'
