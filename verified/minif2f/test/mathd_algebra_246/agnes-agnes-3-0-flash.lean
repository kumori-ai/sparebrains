import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h3 : a * (-3 : ℝ) ^ 4 - b * (-3 : ℝ) ^ 2 + (-3 : ℝ) + 5 = 2 := by
    rw [h₀] at h₂
    exact h₂
  have h4 : f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 := by
    rw [h₀]
  rw [h4]
  have h5 : (-3 : ℝ) ^ 4 = 3 ^ 4 := by norm_num
  have h6 : (-3 : ℝ) ^ 2 = 3 ^ 2 := by norm_num
  rw [h5, h6] at h3
  have h7 : a * 3 ^ 4 - b * 3 ^ 2 + (-3 : ℝ) + 5 = 2 := by
    simpa using h3
  have h8 : a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 = 8 := by
    linarith
  exact h8
