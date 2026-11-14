import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  obtain ⟨ha, hb, hc, hd⟩ := h₀
  have key : ∀ x y : ℝ, 0 < y → x ^ 2 / y ≥ 2 * x - y := by
    intro x y hy
    have hne : y ≠ 0 := ne_of_gt hy
    have h : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
    have hdiv : 0 ≤ (x - y) ^ 2 / y := div_nonneg h (le_of_lt hy)
    have heq : (x - y) ^ 2 / y = x ^ 2 / y - (2 * x - y) := by
      field_simp
      ring
    linarith
  have h1 := key a b hb
  have h2 := key b c hc
  have h3 := key c d hd
  have h4 := key d a ha
  linarith
