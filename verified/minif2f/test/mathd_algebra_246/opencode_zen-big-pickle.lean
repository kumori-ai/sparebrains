import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  rw [h₀] at h₂
  have h_even : a * (3:ℝ)^4 - b * (3:ℝ)^2 = a * (-3)^4 - b * (-3)^2 := by
    ring
  have h_zero : a * (-3)^4 - b * (-3)^2 = 0 := by
    linarith
  calc
    f 3 = a * (3:ℝ)^4 - b * (3:ℝ)^2 + 3 + 5 := h₀ 3
    _ = a * (-3)^4 - b * (-3)^2 + 3 + 5 := by rw [h_even]
    _ = 0 + 3 + 5 := by rw [h_zero]
    _ = 8 := by norm_num
