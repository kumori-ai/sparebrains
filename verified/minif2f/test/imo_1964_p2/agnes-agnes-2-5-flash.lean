import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a,b,c$ are the sides of a triangle. Prove that \[ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c) \leq 3abc  \] -/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have h₁' : 0 < b + c - a := by linarith
  have h₂' : 0 < a + c - b := by linarith
  have h₃' : 0 < a + b - c := by linarith
  have : 0 < (b + c - a) * (a + c - b) * (a + b - c) := by positivity
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
