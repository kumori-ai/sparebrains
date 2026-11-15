import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  simp only [h₀, h₁] at h₂ h₃
  have hxf : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    linear_combination h₂
  have hyf : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    linear_combination h₃
  rcases mul_eq_zero.mp hxf with hx2 | hx3
  · rcases mul_eq_zero.mp hyf with hy2 | hy3
    · exfalso; linarith
    · linarith
  · rcases mul_eq_zero.mp hyf with hy2 | hy3
    · exfalso; linarith
    · exfalso; linarith
