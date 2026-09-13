import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h₂' : a * (-3)^4 - b * (-3)^2 + (-3) + 5 = 2 := by
    simpa [h₀] using h₂
  have hb : b = 9 * a := by
    ring_nf at h₂'
    linarith
  rw [h₀, hb]
  ring_nf
