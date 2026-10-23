import Mathlib

open scoped Nat
open scoped Real

/--
On planet Larky, 7 ligs = 4 lags, and 9 lags = 20 lugs. How many ligs are equivalent to 80 lugs? -/
theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by
  have h₃ : b = 20/9 * c := by linarith
  have h₄ : a = 4/7 * b := by linarith
  have h₅ : a = 4/7 * (20/9 * c) := by linarith
  have h₆ : a = 80/63 * c := by linarith
  linarith
