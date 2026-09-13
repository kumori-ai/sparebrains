import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have hx_eq : x ^ 4 = 5 * x ^ 2 - 6 := by
    rw [h₀, h₁] at h₂
    exact h₂
  have hy_eq : y ^ 4 = 5 * y ^ 2 - 6 := by
    rw [h₀, h₁] at h₃
    exact h₃
  have hx_sq_eq : (x ^ 2) ^ 2 = 5 * x ^ 2 - 6 := by
    calc
      (x ^ 2) ^ 2 = x ^ 4 := by ring
      _ = 5 * x ^ 2 - 6 := hx_eq
  have hy_sq_eq : (y ^ 2) ^ 2 = 5 * y ^ 2 - 6 := by
    calc
      (y ^ 2) ^ 2 = y ^ 4 := by ring
      _ = 5 * y ^ 2 - 6 := hy_eq
  have hx_cases : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    have hprod : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
      have hx_poly : (x ^ 2 - 2) * (x ^ 2 - 3) = (x ^ 2) ^ 2 - 5 * x ^ 2 + 6 := by ring
      rw [hx_poly]
      nlinarith [hx_sq_eq]
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith
  have hy_cases : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    have hprod : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
      have hy_poly : (y ^ 2 - 2) * (y ^ 2 - 3) = (y ^ 2) ^ 2 - 5 * y ^ 2 + 6 := by ring
      rw [hy_poly]
      nlinarith [hy_sq_eq]
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith
  rcases hx_cases with hx2 | hx3
  · rcases hy_cases with hy2 | hy3
    · have hbad : (2:ℝ) < 2 := by simpa [hx2, hy2] using h₄
      linarith
    · rw [hx2, hy3]
      norm_num
  · rcases hy_cases with hy2 | hy3
    · have hbad : (3:ℝ) < 2 := by simpa [hx3, hy2] using h₄
      linarith
    · have hbad : (3:ℝ) < 3 := by simpa [hx3, hy3] using h₄
      linarith
