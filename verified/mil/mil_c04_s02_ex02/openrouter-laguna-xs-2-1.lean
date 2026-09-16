import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex02 {α β : Type*} (f : α → β) (s : Set α) (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x hx
  have h_mem : f x ∈ f '' s := hx
  obtain ⟨y, hy₁, hy₂⟩ := h_mem
  have h_eq : x = y := h (hy₂.symm)
  subst h_eq
  exact hy₁
