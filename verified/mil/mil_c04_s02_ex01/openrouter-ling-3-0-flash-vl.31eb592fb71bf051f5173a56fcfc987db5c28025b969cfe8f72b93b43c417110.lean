import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex01 {α β : Type*} (f : α → β) (s : Set α) (v : Set β) : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x hx
    have hfx_mem : f x ∈ f '' s := mem_image_of_mem f hx
    have hfx_in_v : f x ∈ v := h hfx_mem
    exact mem_preimage.1 hfx_in_v
  · intro h y hy
    rcases hy with ⟨x, hxs, heq⟩
    have hfx_in_v : f x ∈ v := h hxs
    rwa [heq] at hfx_in_v
