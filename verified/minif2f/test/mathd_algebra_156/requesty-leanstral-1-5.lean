import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have hx_eq : x ^ 4 = 5 * x ^ 2 - 6 := by
    calc
      x ^ 4 = f x := by symm; exact h₀ x
      _ = g x := h₂
      _ = 5 * x ^ 2 - 6 := h₁ x
  have hy_eq : y ^ 4 = 5 * y ^ 2 - 6 := by
    calc
      y ^ 4 = f y := by symm; exact h₀ y
      _ = g y := h₃
      _ = 5 * y ^ 2 - 6 := h₁ y
  have hx_factor : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    calc
      (x ^ 2 - 2) * (x ^ 2 - 3) = x ^ 4 - 5 * x ^ 2 + 6 := by ring
      _ = (5 * x ^ 2 - 6) - 5 * x ^ 2 + 6 := by rw [hx_eq]
      _ = 0 := by ring
  have hy_factor : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    calc
      (y ^ 2 - 2) * (y ^ 2 - 3) = y ^ 4 - 5 * y ^ 2 + 6 := by ring
      _ = (5 * y ^ 2 - 6) - 5 * y ^ 2 + 6 := by rw [hy_eq]
      _ = 0 := by ring
  have hx_cases : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hx_factor with h | h
    · left; linarith
    · right; linarith
  have hy_cases : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hy_factor with h | h
    · left; linarith
    · right; linarith
  rcases hx_cases with hx2 | hx3
  · -- x^2 = 2
    rcases hy_cases with hy2 | hy3
    · -- y^2 = 2
      linarith
    · -- y^2 = 3
      linarith
  · -- x^2 = 3
    rcases hy_cases with hy2 | hy3
    · -- y^2 = 2
      linarith
    · -- y^2 = 3
      linarith
