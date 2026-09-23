import Mathlib

open scoped Nat
open scoped Real

/--
If a snack-size tin of peaches has $40$ calories and is $2\%$ of a person's daily caloric requirement, how many calories fulfill a person's daily caloric requirement? -/
theorem mathd_algebra_24 (x : ℝ) (h₀ : x / 50 = 40) : x = 2000 := by
  have h₁ : x = 40 * 50 := by { linarith [h₀] }
  have h₂ : 2000 = 2 * 100 * 10 := by { norm_num }
  have h₃ : 2000 = 2000 := rfl
  have h₄ : 40 * 50 = 2000 := by { norm_num }
  have h₅ : 2000 = 2000 := rfl
  have h₆ : x = 2000 := by { linarith [h₁, h₄] }
  exact h₆
