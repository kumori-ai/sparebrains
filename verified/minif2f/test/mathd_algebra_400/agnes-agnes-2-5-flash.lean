import Mathlib

open scoped Nat
open scoped Real

/-- Five plus $500\%$ of $10$ is the same as $110\%$ of what number? -/
theorem mathd_algebra_400 (x : ℝ) (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) : x = 50 := by
  have h₁ : (500 : ℝ) / 100 * 10 = 50 := by norm_num
  have h₂ : (110 : ℝ) / 100 * x = 1.1 * x := by norm_num
  have h₃ : (5 : ℝ) + 500 / 100 * 10 = 55 := by
    norm_num [h₁]
  have h₄ : (110 : ℝ) / 100 * x = 110 / 100 * x := by rfl
  rw [h₃] at h₀
  norm_num at h₀
  linarith
