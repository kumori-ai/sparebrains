import Mathlib

/-- Mathematics in Lean, Chapter 3 §2 (The Existential Quantifier), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s02_ex04 {a b c : ℕ} (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨k, hk⟩
  rcases divbc with ⟨l, hl⟩
  refine ⟨k * l, ?_⟩
  calc
    c = b * l := hl
    _ = (a * k) * l := by rw [hk]
    _ = a * (k * l) := by ring
