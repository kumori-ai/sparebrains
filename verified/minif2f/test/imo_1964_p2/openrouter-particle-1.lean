import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a,b,c$ are the sides of a triangle. Prove that \[ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c) \leq 3abc  \] -/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have h_ab : 0 < a + b - c := by linarith [h₁]
  have h_bc : 0 < b + c - a := by linarith [h₃]
  have h_ca : 0 < c + a - b := by linarith [h₂]
  have h1 : 0 ≤ (a - b) ^ 2 * (a + b - c) := by
    exact mul_nonneg (sq_nonneg (a - b)) (le_of_lt h_ab)
  have h2 : 0 ≤ (b - c) ^ 2 * (b + c - a) := by
    exact mul_nonneg (sq_nonneg (b - c)) (le_of_lt h_bc)
  have h3 : 0 ≤ (c - a) ^ 2 * (c + a - b) := by
    exact mul_nonneg (sq_nonneg (c - a)) (le_of_lt h_ca)
  have hT :
      0 ≤ (a - b) ^ 2 * (a + b - c) + (b - c) ^ 2 * (b + c - a) +
        (c - a) ^ 2 * (c + a - b) := by
    nlinarith [h1, h2, h3]
  have h_id :
      2 * (3 * a * b * c -
          (a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c))) =
        (a - b) ^ 2 * (a + b - c) + (b - c) ^ 2 * (b + c - a) +
          (c - a) ^ 2 * (c + a - b) := by
    ring
  nlinarith [hT, h_id]
