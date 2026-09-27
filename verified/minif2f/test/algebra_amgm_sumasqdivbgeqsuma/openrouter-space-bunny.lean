import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  have ha : 0 < a := h₀.1
  have hb : 0 < b := h₀.2.1
  have hc : 0 < c := h₀.2.2.1
  have hd : 0 < d := h₀.2.2.2
  have hab : 0 ≤ a ^ 2 / b + b - 2 * a := by
    have h : a ^ 2 / b + b - 2 * a = (a - b) ^ 2 / b := by
      field_simp
      ring
    rw [h]
    exact div_nonneg (sq_nonneg _) (le_of_lt hb)
  have hbc : 0 ≤ b ^ 2 / c + c - 2 * b := by
    have h : b ^ 2 / c + c - 2 * b = (b - c) ^ 2 / c := by
      field_simp
      ring
    rw [h]
    exact div_nonneg (sq_nonneg _) (le_of_lt hc)
  have hcd : 0 ≤ c ^ 2 / d + d - 2 * c := by
    have h : c ^ 2 / d + d - 2 * c = (c - d) ^ 2 / d := by
      field_simp
      ring
    rw [h]
    exact div_nonneg (sq_nonneg _) (le_of_lt hd)
  have hda : 0 ≤ d ^ 2 / a + a - 2 * d := by
    have h : d ^ 2 / a + a - 2 * d = (d - a) ^ 2 / a := by
      field_simp
      ring
    rw [h]
    exact div_nonneg (sq_nonneg _) (le_of_lt ha)
  nlinarith [hab, hbc, hcd, hda]
