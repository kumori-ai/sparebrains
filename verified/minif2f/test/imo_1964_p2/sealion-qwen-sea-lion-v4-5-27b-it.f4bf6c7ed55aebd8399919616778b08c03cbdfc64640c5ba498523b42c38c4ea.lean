import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a,b,c$ are the sides of a triangle. Prove that \[ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c) \leq 3abc  \] -/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have h₁' : 0 < a + b - c := by linarith
  have h₂' : 0 < b + c - a := by linarith
  have h₃' : 0 < c + a - b := by linarith
  have h_id : 3 * a * b * c - (a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c)) = 
      (1 / 2 : ℝ) * ((a + b - c) * (a - b) ^ 2 + (b + c - a) * (b - c) ^ 2 + (c + a - b) * (c - a) ^ 2) := by
    ring
  have h_nonneg : 0 ≤ (a + b - c) * (a - b) ^ 2 + (b + c - a) * (b - c) ^ 2 + (c + a - b) * (c - a) ^ 2 := by
    have h₁'' : 0 ≤ (a + b - c) * (a - b) ^ 2 := by
      exact mul_nonneg h₁'.le (sq_nonneg (a - b))
    have h₂'' : 0 ≤ (b + c - a) * (b - c) ^ 2 := by
      exact mul_nonneg h₂'.le (sq_nonneg (b - c))
    have h₃'' : 0 ≤ (c + a - b) * (c - a) ^ 2 := by
      exact mul_nonneg h₃'.le (sq_nonneg (c - a))
    linarith
  have h_ineq : 0 ≤ 3 * a * b * c - (a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c)) := by
    rw [h_id]
    exact mul_nonneg (by norm_num) h_nonneg
  linarith
