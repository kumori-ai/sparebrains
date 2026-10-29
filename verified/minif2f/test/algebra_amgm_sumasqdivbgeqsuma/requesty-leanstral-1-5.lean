import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have aux (x y : ℝ) (hy : 0 < y) : x ^ 2 / y + y ≥ 2 * x := by
    have hsq : (x - y) ^ 2 ≥ 0 := sq_nonneg _
    field_simp [hy.ne.symm]
    nlinarith
  have h1 : a ^ 2 / b + b ≥ 2 * a := aux a b hb
  have h2 : b ^ 2 / c + c ≥ 2 * b := aux b c hc
  have h3 : c ^ 2 / d + d ≥ 2 * c := aux c d hd
  have h4 : d ^ 2 / a + a ≥ 2 * d := aux d a ha
  have hsum : (a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a) + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    linarith
  linarith
