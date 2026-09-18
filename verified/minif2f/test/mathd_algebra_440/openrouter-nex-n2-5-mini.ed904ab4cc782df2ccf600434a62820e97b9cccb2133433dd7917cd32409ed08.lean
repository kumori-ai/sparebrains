import Mathlib

open scoped Nat
open scoped Real

/--
Jasmine drank 1.5 pints of water on the first 3 miles of her hike. If she continued at this rate, how many pints of water would she drink in the next 10 miles? -/
theorem mathd_algebra_440 (x : ℝ) (h₀ : 3 / 2 / 3 = x / 10) : x = 5 := by
  have h₁ : x = 5 := by
    have h₂ : x / 10 = 1 / 2 := by
      rw [← h₀]
      norm_num
    have h₃ : x = 5 := by
      apply_fun (fun y : ℝ => y * 10) at h₂
      norm_num at h₂
      exact h₂
    exact h₃
  exact h₁
