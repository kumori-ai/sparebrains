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
      x ^ 4 = f x := by rw [← h₀ x]
      _ = g x := h₂
      _ = 5 * x ^ 2 - 6 := h₁ x
  have hy_eq : y ^ 4 = 5 * y ^ 2 - 6 := by
    calc
      y ^ 4 = f y := by rw [← h₀ y]
      _ = g y := h₃
      _ = 5 * y ^ 2 - 6 := h₁ y
  have hx_prod : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    nlinarith [hx_eq]
  have hy_prod : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    nlinarith [hy_eq]
  have hx2_or : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    rcases mul_eq_zero.mp hx_prod with hx2 | hx3
    · left; linarith
    · right; linarith
  have hy2_or : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    rcases mul_eq_zero.mp hy_prod with hy2 | hy3
    · left; linarith
    · right; linarith
  rcases hx2_or with hx2 | hx3
  · rcases hy2_or with hy2 | hy3
    · exfalso; linarith
    · nlinarith
  · exfalso
    have hy_gt : 3 < y ^ 2 := by linarith
    rcases hy2_or with hy2 | hy3
    · linarith
    · linarith
