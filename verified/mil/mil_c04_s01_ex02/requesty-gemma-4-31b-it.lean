import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  rcases hx with ⟨hxs, hx_not_tu⟩
  rcases not_or.mp hx_not_tu with ⟨hxt, hxu⟩
  exact ⟨⟨hxs, hxt⟩, hxu⟩
