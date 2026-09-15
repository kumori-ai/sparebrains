import Mathlib

open scoped Nat
open scoped Real

/--
If a snack-size tin of peaches has $40$ calories and is $2\%$ of a person's daily caloric requirement, how many calories fulfill a person's daily caloric requirement? -/
theorem mathd_algebra_24 (x : ℝ) (h₀ : x / 50 = 40) : x = 2000 := by
  have h₁ : (50 : ℝ) ≠ 0 := by norm_num
  calc
    x = x / 50 * 50 := by field_simp
    _ = 40 * 50 := by rw [h₀]
    _ = 2000 := by norm_num
