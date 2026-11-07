import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have hx : x ^ 4 = 5 * x ^ 2 - 6 := by
    have h := h₂
    simp only [h₀, h₁] at h
    exact h
  have hy : y ^ 4 = 5 * y ^ 2 - 6 := by
    have h := h₃
    simp only [h₀, h₁] at h
    exact h
  have hx2 : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    have h : (x ^ 2 - 2) * (x ^ 2 - 3) = x ^ 4 - 5 * x ^ 2 + 6 := by ring
    rw [h, hx]
    ring
  have hy2 : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    have h : (y ^ 2 - 2) * (y ^ 2 - 3) = y ^ 4 - 5 * y ^ 2 + 6 := by ring
    rw [h, hy]
    ring
  rcases mul_eq_zero.mp hx2 with hxA | hxB
  · rcases mul_eq_zero.mp hy2 with hyA | hyB
    · have hxa : x ^ 2 = 2 := by linarith
      have hya : y ^ 2 = 2 := by linarith
      linarith
    · have hxa : x ^ 2 = 2 := by linarith
      have hyb : y ^ 2 = 3 := by linarith
      linarith
  · rcases mul_eq_zero.mp hy2 with hyA | hyB
    · have hxb : x ^ 2 = 3 := by linarith
      have hya : y ^ 2 = 2 := by linarith
      linarith
    · have hxb : x ^ 2 = 3 := by linarith
      have hyb : y ^ 2 = 3 := by linarith
      linarith
