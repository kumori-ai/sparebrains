import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  obtain ⟨ha, hb, hc, hd⟩ := h₀
  have hane : a ≠ 0 := ne_of_gt ha
  have hbne : b ≠ 0 := ne_of_gt hb
  have hcne : c ≠ 0 := ne_of_gt hc
  have hdne : d ≠ 0 := ne_of_gt hd
  have h1 : 2 * a ≤ a ^ 2 / b + b := by
    have h : (0 : ℝ) ≤ (a - b) ^ 2 / b := div_nonneg (sq_nonneg _) hb.le
    have heq : (a - b) ^ 2 / b = a ^ 2 / b + b - 2 * a := by
      field_simp
      ring
    linarith
  have h2 : 2 * b ≤ b ^ 2 / c + c := by
    have h : (0 : ℝ) ≤ (b - c) ^ 2 / c := div_nonneg (sq_nonneg _) hc.le
    have heq : (b - c) ^ 2 / c = b ^ 2 / c + c - 2 * b := by
      field_simp
      ring
    linarith
  have h3 : 2 * c ≤ c ^ 2 / d + d := by
    have h : (0 : ℝ) ≤ (c - d) ^ 2 / d := div_nonneg (sq_nonneg _) hd.le
    have heq : (c - d) ^ 2 / d = c ^ 2 / d + d - 2 * c := by
      field_simp
      ring
    linarith
  have h4 : 2 * d ≤ d ^ 2 / a + a := by
    have h : (0 : ℝ) ≤ (d - a) ^ 2 / a := div_nonneg (sq_nonneg _) ha.le
    have heq : (d - a) ^ 2 / a = d ^ 2 / a + a - 2 * d := by
      field_simp
      ring
    linarith
  linarith
