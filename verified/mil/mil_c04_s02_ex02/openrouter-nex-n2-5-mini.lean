import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex02 {α β : Type*} (f : α → β) (s : Set α) (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x hx
  simp only [Set.mem_preimage, Set.mem_image] at hx
  obtain ⟨y, hy, hfy⟩ := hx
  exact (h hfy) ▸ hy
