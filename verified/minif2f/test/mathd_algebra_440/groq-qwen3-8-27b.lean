import Mathlib

open scoped Nat
open scoped Real

/--
Jasmine drank 1.5 pints of water on the first 3 miles of her hike. If she continued at this rate, how many pints of water would she drink in the next 10 miles? -/
theorem mathd_algebra_440 (x : ℝ) (h₀ : 3 / 2 / 3 = x / 10) : x = 5 := by
  have h1 : x / 10 = 1 / 2 := by
    rw [← h₀]
    norm_num
  rw [div_eq_iff (by norm_num : (10 : ℝ) ≠ 0)] at h1
  norm_num at h1
  exact h1
