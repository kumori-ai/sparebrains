import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  rcases hx with ⟨hxin, hxnot⟩
  have hxnot_t : x ∉ t := by
    intro hxt
    exact hxnot (Or.inl hxt)
  have hxnot_u : x ∉ u := by
    intro hxu
    exact hxnot (Or.inr hxu)
  exact ⟨⟨hxin, hxnot_t⟩, hxnot_u⟩
