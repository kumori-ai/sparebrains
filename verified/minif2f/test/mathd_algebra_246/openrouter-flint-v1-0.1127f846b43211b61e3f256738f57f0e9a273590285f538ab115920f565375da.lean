import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have hneg : a * (-3:ℝ)^4 - b * (-3:ℝ)^2 + (-3:ℝ) + 5 = 2 := by
    exact (h₀ (-3)).symm.trans h₂
  have hpos : a * (3:ℝ)^4 - b * (3:ℝ)^2 + (3:ℝ) + 5 = 8 := by
    have hEq : a * (3:ℝ)^4 - b * (3:ℝ)^2 + (3:ℝ) + 5 =
        a * (-3:ℝ)^4 - b * (-3:ℝ)^2 + (-3:ℝ) + 5 + 6 := by
      ring_nf
    rw [hEq, hneg]
    norm_num
  rw [h₀ 3]
  exact hpos
