import Mathlib

/-- Mathematics in Lean, Chapter 3 §2 (The Existential Quantifier), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s02_ex05 {a b c : ℕ} (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  obtain ⟨k, hk⟩ := divab
  obtain ⟨l, hl⟩ := divac
  exact ⟨k + l, by rw [hk, hl]; ring⟩
