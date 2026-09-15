import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  have h₁ : a ^ 2 / b + b ≥ 2 * a := by
    have h₂ : 0 ≤ (a - b) ^ 2 / b := by
      exact div_nonneg (sq_nonneg (a - b)) (le_of_lt h₀.2.1)
    calc
      a ^ 2 / b + b = 2 * a + (a - b) ^ 2 / b := by
        field_simp [h₀.2.1.ne']
        ring
      _ ≥ 2 * a := by linarith

  have h₂ : b ^ 2 / c + c ≥ 2 * b := by
    have h₃ : 0 ≤ (b - c) ^ 2 / c := by
      exact div_nonneg (sq_nonneg (b - c)) (le_of_lt h₀.2.2.1)
    calc
      b ^ 2 / c + c = 2 * b + (b - c) ^ 2 / c := by
        field_simp [h₀.2.2.1.ne']
        ring
      _ ≥ 2 * b := by linarith

  have h₃ : c ^ 2 / d + d ≥ 2 * c := by
    have h₄ : 0 ≤ (c - d) ^ 2 / d := by
      exact div_nonneg (sq_nonneg (c - d)) (le_of_lt h₀.2.2.2)
    calc
      c ^ 2 / d + d = 2 * c + (c - d) ^ 2 / d := by
        field_simp [h₀.2.2.2.ne']
        ring
      _ ≥ 2 * c := by linarith

  have h₄ : d ^ 2 / a + a ≥ 2 * d := by
    have h₅ : 0 ≤ (d - a) ^ 2 / a := by
      exact div_nonneg (sq_nonneg (d - a)) (le_of_lt h₀.1)
    calc
      d ^ 2 / a + a = 2 * d + (d - a) ^ 2 / a := by
        field_simp [h₀.1.ne']
        ring
      _ ≥ 2 * d := by linarith

  have h₅ :
      (a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a) + (a + b + c + d) ≥
        2 * (a + b + c + d) := by
    linarith [h₁, h₂, h₃, h₄]

  linarith
