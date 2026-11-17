import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  have h1 : a ^ 2 / b + b ≥ 2 * a := by
    have hb : 0 < b := h₀.2.1
    have h : a ^ 2 / b + b - 2 * a = (a - b) ^ 2 / b := by
      field_simp [hb.ne']
      ring
    have hnonneg : 0 ≤ (a - b) ^ 2 / b :=
      div_nonneg (sq_nonneg (a - b)) (le_of_lt hb)
    linarith
  have h2 : b ^ 2 / c + c ≥ 2 * b := by
    have hc : 0 < c := h₀.2.2.1
    have h : b ^ 2 / c + c - 2 * b = (b - c) ^ 2 / c := by
      field_simp [hc.ne']
      ring
    have hnonneg : 0 ≤ (b - c) ^ 2 / c :=
      div_nonneg (sq_nonneg (b - c)) (le_of_lt hc)
    linarith
  have h3 : c ^ 2 / d + d ≥ 2 * c := by
    have hd : 0 < d := h₀.2.2.2
    have h : c ^ 2 / d + d - 2 * c = (c - d) ^ 2 / d := by
      field_simp [hd.ne']
      ring
    have hnonneg : 0 ≤ (c - d) ^ 2 / d :=
      div_nonneg (sq_nonneg (c - d)) (le_of_lt hd)
    linarith
  have h4 : d ^ 2 / a + a ≥ 2 * d := by
    have ha : 0 < a := h₀.1
    have h : d ^ 2 / a + a - 2 * d = (d - a) ^ 2 / a := by
      field_simp [ha.ne']
      ring
    have hnonneg : 0 ≤ (d - a) ^ 2 / a :=
      div_nonneg (sq_nonneg (d - a)) (le_of_lt ha)
    linarith
  linarith [h1, h2, h3, h4]
