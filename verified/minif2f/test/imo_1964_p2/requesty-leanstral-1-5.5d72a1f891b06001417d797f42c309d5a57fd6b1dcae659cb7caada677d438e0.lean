import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a,b,c$ are the sides of a triangle. Prove that \[ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c) \leq 3abc  \] -/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  rcases h₀ with ⟨ha, hb, hc⟩
  have habc : 0 < a + b - c := by linarith
  have hbca : 0 < b + c - a := by linarith
  have hcab : 0 < c + a - b := by linarith
  have h_sum_nonneg : 0 ≤ (a + b - c) * (a - b)^2 + (b + c - a) * (b - c)^2 + (c + a - b) * (c - a)^2 := by
    have h1 : 0 ≤ (a + b - c) * (a - b)^2 := mul_nonneg (by linarith) (pow_two_nonneg _)
    have h2 : 0 ≤ (b + c - a) * (b - c)^2 := mul_nonneg (by linarith) (pow_two_nonneg _)
    have h3 : 0 ≤ (c + a - b) * (c - a)^2 := mul_nonneg (by linarith) (pow_two_nonneg _)
    exact add_nonneg (add_nonneg h1 h2) h3
  have h_eq : a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) - 3 * a * b * c =
      -((a + b - c) * (a - b)^2 + (b + c - a) * (b - c)^2 + (c + a - b) * (c - a)^2) / 2 := by
    ring
  linarith
