import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have h1 : a ^ 2 / b + b ≥ 2 * a := by
    have h : a ^ 2 / b + b - 2 * a ≥ 0 := by
      calc
        a ^ 2 / b + b - 2 * a = (a - b) ^ 2 / b := by
          field_simp [hb.ne.symm]
          ring
        _ ≥ 0 := div_nonneg (by nlinarith) (by linarith)
    linarith
  have h2 : b ^ 2 / c + c ≥ 2 * b := by
    have h : b ^ 2 / c + c - 2 * b ≥ 0 := by
      calc
        b ^ 2 / c + c - 2 * b = (b - c) ^ 2 / c := by
          field_simp [hc.ne.symm]
          ring
        _ ≥ 0 := div_nonneg (by nlinarith) (by linarith)
    linarith
  have h3 : c ^ 2 / d + d ≥ 2 * c := by
    have h : c ^ 2 / d + d - 2 * c ≥ 0 := by
      calc
        c ^ 2 / d + d - 2 * c = (c - d) ^ 2 / d := by
          field_simp [hd.ne.symm]
          ring
        _ ≥ 0 := div_nonneg (by nlinarith) (by linarith)
    linarith
  have h4 : d ^ 2 / a + a ≥ 2 * d := by
    have h : d ^ 2 / a + a - 2 * d ≥ 0 := by
      calc
        d ^ 2 / a + a - 2 * d = (d - a) ^ 2 / a := by
          field_simp [ha.ne.symm]
          ring
        _ ≥ 0 := div_nonneg (by nlinarith) (by linarith)
    linarith
  linarith
