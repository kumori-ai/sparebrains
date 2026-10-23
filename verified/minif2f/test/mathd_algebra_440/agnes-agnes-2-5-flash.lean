import Mathlib

open scoped Nat
open scoped Real

/--
Jasmine drank 1.5 pints of water on the first 3 miles of her hike. If she continued at this rate, how many pints of water would she drink in the next 10 miles? -/
theorem mathd_algebra_440 (x : ℝ) (h₀ : 3 / 2 / 3 = x / 10) : x = 5 := by
  have h₁ : x / 10 = (1 : ℝ) / 2 := by
    calc
      x / 10 = 3 / 2 / 3 := by rw [h₀]
      _ = 1 / 2 := by ring
  have h₂ : x = 5 := by
    have h₃ : x = 10 * (1 / 2) := by
      calc
        x = 10 * (x / 10) := by field_simp
        _ = 10 * (1 / 2) := by rw [h₁]
    norm_num at h₃ ⊢
    linarith
  exact h₂
