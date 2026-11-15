import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have h₁ : a ^ 2 / b + b ≥ 2 * a := by
    have : (a - b) ^ 2 / b ≥ 0 := by positivity
    have : (a ^ 2 / b + b) - 2 * a = (a - b) ^ 2 / b := by
      field_simp [ne_of_gt hb]
      ring
    linarith
  have h₂ : b ^ 2 / c + c ≥ 2 * b := by
    have : (b - c) ^ 2 / c ≥ 0 := by positivity
    have : (b ^ 2 / c + c) - 2 * b = (b - c) ^ 2 / c := by
      field_simp [ne_of_gt hc]
      ring
    linarith
  have h₃ : c ^ 2 / d + d ≥ 2 * c := by
    have : (c - d) ^ 2 / d ≥ 0 := by positivity
    have : (c ^ 2 / d + d) - 2 * c = (c - d) ^ 2 / d := by
      field_simp [ne_of_gt hd]
      ring
    linarith
  have h₄ : d ^ 2 / a + a ≥ 2 * d := by
    have : (d - a) ^ 2 / a ≥ 0 := by positivity
    have : (d ^ 2 / a + a) - 2 * d = (d - a) ^ 2 / a := by
      field_simp [ne_of_gt ha]
      ring
    linarith
  have h_sum : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    linarith
  linarith
