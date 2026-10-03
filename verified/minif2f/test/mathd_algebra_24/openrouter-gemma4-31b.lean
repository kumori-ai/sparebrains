import Mathlib

open scoped Nat
open scoped Real

/--
If a snack-size tin of peaches has $40$ calories and is $2\%$ of a person's daily caloric requirement, how many calories fulfill a person's daily caloric requirement? -/
theorem mathd_algebra_24 (x : ℝ) (h₀ : x / 50 = 40) : x = 2000 := by
  have h₁ : x = 40 * 50 := by
    linarith
  norm_num at h₁
  exact h₁
