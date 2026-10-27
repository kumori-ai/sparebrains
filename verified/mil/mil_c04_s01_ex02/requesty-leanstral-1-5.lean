import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  rcases hx with ⟨hxs, hx_not_tu⟩
  have hx_not_t : x ∉ t := by
    intro hxt; apply hx_not_tu; exact Or.inl hxt
  have hx_not_u : x ∉ u := by
    intro hxu; apply hx_not_tu; exact Or.inr hxu
  exact ⟨⟨hxs, hx_not_t⟩, hx_not_u⟩
