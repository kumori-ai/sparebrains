import Mathlib

open scoped Nat
open scoped Real

/--
On planet Larky, 7 ligs = 4 lags, and 9 lags = 20 lugs. How many ligs are equivalent to 80 lugs? -/
theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by
  calc
    63 * a = (7 * a) * 9 := by ring
    _ = (4 * b) * 9 := by rw [h₂]
    _ = 36 * b := by ring
    _ = (9 * b) * 4 := by ring
    _ = (20 * c) * 4 := by rw [h₁]
    _ = 80 * c := by ring
