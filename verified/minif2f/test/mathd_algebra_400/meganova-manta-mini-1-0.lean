import Mathlib

open scoped Nat
open scoped Real

/-- Five plus $500\%$ of $10$ is the same as $110\%$ of what number? -/
theorem mathd_algebra_400 (x : ℝ) (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) : x = 50 := by
  have h₁ : (5 : ℝ) + (500 : ℝ) / (100 : ℝ) * (10 : ℝ) = (55 : ℝ) := by
    ring
  have h₂ : (110 : ℝ) / (100 : ℝ) * x = (11/10 : ℝ) * x := by
    ring
  rw [h₁, h₂] at h₀
  have h₃ : (55 : ℝ) = (11/10 : ℝ) * x := h₀
  field_simp at h₃
  linarith
