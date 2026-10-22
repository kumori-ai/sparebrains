import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have h1 : a ^ 2 / b ≥ 2 * a - b := by
    have h1' : 0 < b := hb
    have h2' : a ^ 2 / b + b ≥ 2 * a := by
      have h3' : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
        nlinarith [sq_nonneg (a - b)]
      have h4' : 0 < b := hb
      field_simp [h4']
      nlinarith
    linarith
  have h2 : b ^ 2 / c ≥ 2 * b - c := by
    have h2' : 0 < c := hc
    have h3' : b ^ 2 / c + c ≥ 2 * b := by
      have h4' : b ^ 2 + c ^ 2 ≥ 2 * b * c := by
        nlinarith [sq_nonneg (b - c)]
      have h5' : 0 < c := hc
      field_simp [h5']
      nlinarith
    linarith
  have h3 : c ^ 2 / d ≥ 2 * c - d := by
    have h3' : 0 < d := hd
    have h4' : c ^ 2 / d + d ≥ 2 * c := by
      have h5' : c ^ 2 + d ^ 2 ≥ 2 * c * d := by
        nlinarith [sq_nonneg (c - d)]
      have h6' : 0 < d := hd
      field_simp [h6']
      nlinarith
    linarith
  have h4 : d ^ 2 / a ≥ 2 * d - a := by
    have h4' : 0 < a := ha
    have h5' : d ^ 2 / a + a ≥ 2 * d := by
      have h6' : d ^ 2 + a ^ 2 ≥ 2 * d * a := by
        nlinarith [sq_nonneg (d - a)]
      have h7' : 0 < a := ha
      field_simp [h7']
      nlinarith
    linarith
  nlinarith
