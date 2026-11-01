import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h3 : a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 = 2 := by
    rw [← h₀ (-3), h₂]
  have h4 : a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 = 8 := by
    norm_num at h3 ⊢
    <;> linarith
  rw [h₀ 3]
  exact h4
