import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have hx : x ^ 4 = 5 * x ^ 2 - 6 := by
    rw [h₀ x, h₁ x] at h₂
    exact h₂
  have hy : y ^ 4 = 5 * y ^ 2 - 6 := by
    rw [h₀ y, h₁ y] at h₃
    exact h₃
  have hx_factor : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    nlinarith [hx]
  have hy_factor : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    nlinarith [hy]
  have hx_cases : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    rcases mul_eq_zero.mp hx_factor with h | h
    · left
      linarith
    · right
      linarith
  have hy_cases : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    rcases mul_eq_zero.mp hy_factor with h | h
    · left
      linarith
    · right
      linarith
  rcases hx_cases with hx2 | hx3 <;> rcases hy_cases with hy2 | hy3
  · linarith
  · linarith
  · linarith
  · linarith
