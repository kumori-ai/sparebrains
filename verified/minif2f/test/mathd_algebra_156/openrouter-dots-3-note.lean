import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have hx : x^4 - 5*x^2 + 6 = 0 := by
    rw [h₀, h₁] at h₂
    linarith
  have hy : y^4 - 5*y^2 + 6 = 0 := by
    rw [h₀, h₁] at h₃
    linarith
  have hx_factor : (x^2 - 2) * (x^2 - 3) = 0 := by
    calc
      (x^2 - 2) * (x^2 - 3) = x^4 - 5*x^2 + 6 := by ring
      _ = 0 := by linarith [hx]
  have hy_factor : (y^2 - 2) * (y^2 - 3) = 0 := by
    calc
      (y^2 - 2) * (y^2 - 3) = y^4 - 5*y^2 + 6 := by ring
      _ = 0 := by linarith [hy]
  have hx_eq : x^2 = 2 ∨ x^2 = 3 := by
    rcases mul_eq_zero.mp hx_factor with h | h
    · left; linarith
    · right; linarith
  have hy_eq : y^2 = 2 ∨ y^2 = 3 := by
    rcases mul_eq_zero.mp hy_factor with h | h
    · left; linarith
    · right; linarith
  rcases hx_eq with hx_eq | hx_eq
  · rcases hy_eq with hy_eq | hy_eq
    · -- x^2 = 2, y^2 = 2
      rw [hx_eq, hy_eq] at h₄
      linarith
    · -- x^2 = 2, y^2 = 3
      rw [hx_eq, hy_eq]
      linarith
  · rcases hy_eq with hy_eq | hy_eq
    · -- x^2 = 3, y^2 = 2
      rw [hx_eq, hy_eq] at h₄
      linarith
    · -- x^2 = 3, y^2 = 3
      rw [hx_eq, hy_eq] at h₄
      linarith
