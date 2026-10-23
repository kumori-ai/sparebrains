import Mathlib

open Function

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 17. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex17 {α : Type*} {β : Type*} {γ : Type*} {g : β → γ} {f : α → β} (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x₁ x₂ h
  have h₁ : f x₁ = f x₂ := by
    apply injg
    simpa using h
  have h₂ : x₁ = x₂ := injf h₁
  exact h₂
