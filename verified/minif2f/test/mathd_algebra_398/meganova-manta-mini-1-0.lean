import Mathlib

open scoped Nat
open scoped Real

/--
On planet Larky, 7 ligs = 4 lags, and 9 lags = 20 lugs. How many ligs are equivalent to 80 lugs? -/
theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by
  rcases h₀ with ⟨ha, hb, hc⟩
  have hb' : b = (20/9) * c := by
    linarith
  have ha' : a = (4/7) * b := by
    linarith
  calc
    63 * a = 63 * ((4/7) * b) := by rw [ha']
    _ = (63 * (4/7)) * b := by ring
    _ = 36 * b := by ring
    _ = 36 * ((20/9) * c) := by rw [hb']
    _ = (36 * (20/9)) * c := by ring
    _ = 80 * c := by ring
