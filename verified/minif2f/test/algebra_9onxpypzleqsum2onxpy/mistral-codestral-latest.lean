import Mathlib

open scoped Nat
open scoped Real

theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h₁ : 0 < x + y := add_pos h₀.1 h₀.2.1
  have h₂ : 0 < y + z := add_pos h₀.2.1 h₀.2.2
  have h₃ : 0 < z + x := add_pos h₀.2.2 h₀.1
  have h₄ : 0 < x + y + z := add_pos (add_pos h₀.1 h₀.2.1) h₀.2.2
  have hdiff : 2 / (x + y) + 2 / (y + z) + 2 / (z + x) - 9 / (x + y + z) ≥ 0 := by
    field_simp [h₁.ne, h₂.ne, h₃.ne, h₄.ne]
    ring_nf
    have hpos : 0 < (x + y) * (y + z) * (z + x) * (x + y + z) := by positivity
    have hnonneg : 0 ≤ 2 * ((x + y) * (y - z)^2 + (y + z) * (z - x)^2 + (z + x) * (x - y)^2) := by
      ring_nf
      have h₅ : (x + y) * (y - z) ^ 2 + (y + z) * (z - x) ^ 2 + (z + x) * (x - y) ^ 2 ≥ 0 := by
        ring_nf
        have h₆ : (x + y) * (y - z) ^ 2 ≥ 0 := by positivity
        have h₇ : (y + z) * (z - x) ^ 2 ≥ 0 := by positivity
        have h₈ : (z + x) * (x - y) ^ 2 ≥ 0 := by positivity
        linarith
      linarith [h₅]
    nlinarith
  linarith [hdiff]
