import Mathlib

open scoped Nat
open scoped Real

/--
Because of redistricting, Liberty Middle School's enrollment increased to 598 students. This is an increase of $4\%$ over last year's enrollment. What was last year's enrollment? -/
theorem mathd_algebra_137 (x : ℕ) (h₀ : ↑x + (4 : ℝ) / (100 : ℝ) * ↑x = 598) : x = 575 := by
  have h₁ : (↑x : ℝ) * (1 + (4 : ℝ) / 100) = 598 := by
    linarith
  have h₂ : (1 : ℝ) + (4 : ℝ) / 100 = 104 / 100 := by
    ring
  rw [h₂] at h₁
  have h₃ : (↑x : ℝ) = 598 * 100 / 104 := by
    field_simp at h₁
    linarith
  have h₄ : (598 : ℝ) * 100 / 104 = (575 : ℝ) := by
    norm_num
  rw [h₄] at h₃
  exact_mod_cast h₃
