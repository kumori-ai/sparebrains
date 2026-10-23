import Mathlib

open scoped Nat
open scoped Real

/--
Jasmine drank 1.5 pints of water on the first 3 miles of her hike. If she continued at this rate, how many pints of water would she drink in the next 10 miles? -/
theorem mathd_algebra_440 (x : ℝ) (h₀ : 3 / 2 / 3 = x / 10) : x = 5 := by
  have h₁ : (1 : ℝ) / 2 = x / 10 := by
    norm_num at h₀ ⊢
    <;> simpa using h₀
  have h₂ : x = 5 := by
    have h₃ : x = 10 * ((1 : ℝ) / 2) := by
      apply mul_left_cancel₀ (show ((1 : ℝ) / 10) ≠ 0 by norm_num)
      field_simp at h₁ ⊢
      <;> nlinarith
    rw [h₃]
    norm_num
  exact h₂
