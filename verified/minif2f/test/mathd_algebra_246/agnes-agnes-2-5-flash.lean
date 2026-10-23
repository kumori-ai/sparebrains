import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h₃ : f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 := by rw [h₀]
  have h₄ : f (-3) = a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 := by rw [h₀]
  have h₅ : a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 = (a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5) + 6 := by ring
  have h₆ : f 3 = f (-3) + 6 := by linarith
  rw [h₂] at h₆
  linarith
