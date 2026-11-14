import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have h₁ : a ^ 2 / b + b ≥ 2 * a := by
    have : a ^ 2 / b + b - 2 * a = (a - b) ^ 2 / b := by
      field_simp [hb.ne']
      ring
    have : 0 ≤ (a - b) ^ 2 / b := by positivity
    linarith
  have h₂ : b ^ 2 / c + c ≥ 2 * b := by
    have : b ^ 2 / c + c - 2 * b = (b - c) ^ 2 / c := by
      field_simp [hc.ne']
      ring
    have : 0 ≤ (b - c) ^ 2 / c := by positivity
    linarith
  have h₃ : c ^ 2 / d + d ≥ 2 * c := by
    have : c ^ 2 / d + d - 2 * c = (c - d) ^ 2 / d := by
      field_simp [hd.ne']
      ring
    have : 0 ≤ (c - d) ^ 2 / d := by positivity
    linarith
  have h₄ : d ^ 2 / a + a ≥ 2 * d := by
    have : d ^ 2 / a + a - 2 * d = (d - a) ^ 2 / a := by
      field_simp [ha.ne']
      ring
    have : 0 ≤ (d - a) ^ 2 / a := by positivity
    linarith
  linarith
