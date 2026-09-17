import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h₃ : a * (-3 : ℝ) ^ 4 - b * (-3 : ℝ) ^ 2 + (-3 : ℝ) + 5 = 2 := by
    simpa [h₀] using h₂
  have h₄ : a * (-3 : ℝ) ^ 4 - b * (-3 : ℝ) ^ 2 = 0 := by linarith
  have h₅ : (-3 : ℝ) ^ 4 = (3 : ℝ) ^ 4 := by norm_num
  have h₆ : (-3 : ℝ) ^ 2 = (3 : ℝ) ^ 2 := by norm_num
  have h₇ : a * (3 : ℝ) ^ 4 - b * (3 : ℝ) ^ 2 = 0 := by
    simpa [h₅, h₆] using h₄
  calc
    f 3 = a * (3 : ℝ) ^ 4 - b * (3 : ℝ) ^ 2 + 3 + 5 := by simpa [h₀]
    _ = 8 := by rw [h₇]; norm_num
