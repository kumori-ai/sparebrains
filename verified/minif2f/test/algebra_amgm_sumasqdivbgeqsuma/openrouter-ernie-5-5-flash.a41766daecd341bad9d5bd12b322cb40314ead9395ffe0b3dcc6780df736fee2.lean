import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  have ha : 0 < a := h₀.1
  have hb : 0 < b := h₀.2.1
  have hc : 0 < c := h₀.2.2.1
  have hd : 0 < d := h₀.2.2.2
  have h1 : a ^ 2 / b ≥ 2 * a - b := by
    rw [ge_iff_le, le_div_iff₀ hb]
    nlinarith [sq_nonneg (a - b)]
  have h2 : b ^ 2 / c ≥ 2 * b - c := by
    rw [ge_iff_le, le_div_iff₀ hc]
    nlinarith [sq_nonneg (b - c)]
  have h3 : c ^ 2 / d ≥ 2 * c - d := by
    rw [ge_iff_le, le_div_iff₀ hd]
    nlinarith [sq_nonneg (c - d)]
  have h4 : d ^ 2 / a ≥ 2 * d - a := by
    rw [ge_iff_le, le_div_iff₀ ha]
    nlinarith [sq_nonneg (d - a)]
  linarith
