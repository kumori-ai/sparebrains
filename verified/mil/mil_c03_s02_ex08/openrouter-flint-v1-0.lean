import Mathlib

open Function

/-- Mathematics in Lean, Chapter 3 §2 (The Existential Quantifier), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s02_ex08 {α : Type*} {β : Type*} {γ : Type*} {g : β → γ} {f : α → β} (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  unfold Surjective
  intro z
  rcases surjg z with ⟨b, hb⟩
  rcases surjf b with ⟨a, fa⟩
  refine ⟨a, ?_⟩
  calc
    g (f a) = g b := by rw [fa]
    _ = z := by rw [hb]
