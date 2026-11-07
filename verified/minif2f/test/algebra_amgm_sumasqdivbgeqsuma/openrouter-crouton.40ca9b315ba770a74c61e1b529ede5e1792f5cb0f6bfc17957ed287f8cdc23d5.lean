import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  obtain ⟨ha, hb, hc, hd⟩ := h₀
  have key : ∀ x y : ℝ, 0 < y → x ^ 2 / y + y ≥ 2 * x := by
    intro x y hy
    have hyne : y ≠ 0 := hy.ne'
    have h1 : 0 ≤ (x - y) ^ 2 / y := div_nonneg (sq_nonneg _) hy.le
    have h2 : (x - y) ^ 2 / y = x ^ 2 / y + y - 2 * x := by
      field_simp
      ring
    linarith
  have h_a := key a b hb
  have h_b := key b c hc
  have h_c := key c d hd
  have h_d := key d a ha
  linarith
