import Mathlib

/-- Mathematics in Lean, Chapter 3 §2 (The Existential Quantifier), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s02_ex04 {a b c : ℕ} (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  obtain ⟨k₁, hk₁⟩ := divab
  obtain ⟨k₂, hk₂⟩ := divbc
  use k₁ * k₂
  rw [hk₂, hk₁]
  ring
