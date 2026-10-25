import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have hx : x ^ 4 = 5 * x ^ 2 - 6 := by
    rw [h₀, h₁] at h₂
    exact h₂
  have hy : y ^ 4 = 5 * y ^ 2 - 6 := by
    rw [h₀, h₁] at h₃
    exact h₃
  have hx_eq : x ^ 4 - 5 * x ^ 2 + 6 = 0 := by
    linarith [hx]
  have hy_eq : y ^ 4 - 5 * y ^ 2 + 6 = 0 := by
    linarith [hy]
  have hx_fact : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    ring_nf
    linarith [hx_eq]
  have hy_fact : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    ring_nf
    linarith [hy_eq]
  have hx_cases : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    obtain (h | h) : x ^ 2 - 2 = 0 ∨ x ^ 2 - 3 = 0 := by
      apply mul_eq_zero.mp
      exact hx_fact
    · left
      linarith
    · right
      linarith
  have hy_cases : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    obtain (h | h) : y ^ 2 - 2 = 0 ∨ y ^ 2 - 3 = 0 := by
      apply mul_eq_zero.mp
      exact hy_fact
    · left
      linarith
    · right
      linarith
  rcases hx_cases with (hx2 | hx3)
  · rcases hy_cases with (hy2 | hy3)
    · exfalso
      linarith
    · have hxy : y ^ 2 - x ^ 2 = 1 := by
        have : y ^ 2 = 3 := by assumption
        have : x ^ 2 = 2 := by assumption
        linarith
      exact hxy
  · rcases hy_cases with (hy2 | hy3)
    · exfalso
      linarith
    · exfalso
      linarith
