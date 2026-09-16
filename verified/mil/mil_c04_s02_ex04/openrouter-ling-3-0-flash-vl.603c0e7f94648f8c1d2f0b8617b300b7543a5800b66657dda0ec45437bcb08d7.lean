import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex04 {α β : Type*} (f : α → β) (u : Set β) (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y hy
  rcases h y with ⟨x, hx⟩
  have hxy : f x ∈ u := by rw [hx]; exact hy
  rw [← hx]
  exact mem_image_of_mem f (mem_preimage.1 hxy)
