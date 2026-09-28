import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have hx : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    have h := h₂
    rw [h₀ x, h₁ x] at h
    nlinarith [h]
  have hy : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    have h := h₃
    rw [h₀ y, h₁ y] at h
    nlinarith [h]
  rcases mul_eq_zero.mp hx with hx₂ | hx₃
  · rcases mul_eq_zero.mp hy with hy₂ | hy₃
    · linarith [h₄, hx₂, hy₂]
    · linarith [h₄, hx₂, hy₃]
  · rcases mul_eq_zero.mp hy with hy₂ | hy₃
    · linarith [h₄, hx₃, hy₂]
    · linarith [h₄, hx₃, hy₃]
