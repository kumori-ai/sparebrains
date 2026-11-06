import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have hAt3 : f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 := h₀ 3
  have hAtNeg3 : f (-3) = a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 := h₀ (-3)
  have hEqNeg : a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 = 2 := by
    rw [h₂] at hAtNeg3
    exact hAtNeg3.symm
  rw [hAt3]
  have hEq : a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 = 8 := by
    ring_nf at hEqNeg
    ring_nf
    nlinarith
  exact hEq
