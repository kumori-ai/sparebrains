import Mathlib

open scoped Nat
open scoped Real

/--
Because of redistricting, Liberty Middle School's enrollment increased to 598 students. This is an increase of $4\%$ over last year's enrollment. What was last year's enrollment? -/
theorem mathd_algebra_137 (x : ℕ) (h₀ : ↑x + (4 : ℝ) / (100 : ℝ) * ↑x = 598) : x = 575 := by
  norm_num at h₀
  have h₁ : (x : ℝ) = 575 := by linarith
  exact_mod_cast h₁
