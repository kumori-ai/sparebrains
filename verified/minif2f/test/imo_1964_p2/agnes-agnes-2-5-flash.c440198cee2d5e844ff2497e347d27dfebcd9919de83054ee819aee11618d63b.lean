import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a,b,c$ are the sides of a triangle. Prove that \[ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c) \leq 3abc  \] -/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have h₄ : 0 < b + c - a := by linarith
  have h₅ : 0 < a + c - b := by linarith
  have h₆ : 0 < a + b - c := by linarith
  have h₇ : 0 < (b + c - a) * (a + c - b) := by nlinarith
  have h₈ : 0 < (b + c - a) * (a + b - c) := by nlinarith
  have h₉ : 0 < (a + c - b) * (a + b - c) := by nlinarith
  have h₁₀ : 0 ≤ (a - b) ^ 2 * (c + a - b) + (b - c) ^ 2 * (a + b - c) + (c - a) ^ 2 * (b + c - a) := by
    have h₁₀a : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
    have h₁₀b : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
    have h₁₀c : 0 ≤ (c - a) ^ 2 := sq_nonneg (c - a)
    nlinarith
  nlinarith [mul_self_nonneg (a * (b + c - a) - b * (a + c - b)),
             mul_self_nonneg (b * (a + c - b) - c * (a + b - c)),
             mul_self_nonneg (c * (a + b - c) - a * (b + c - a))]
