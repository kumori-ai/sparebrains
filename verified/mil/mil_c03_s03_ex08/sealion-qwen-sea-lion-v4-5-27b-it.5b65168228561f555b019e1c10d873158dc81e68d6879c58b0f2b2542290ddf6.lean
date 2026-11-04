import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex08 {α : Type*} (P : α → Prop) (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro ⟨x, hx⟩
  exact h x hx
