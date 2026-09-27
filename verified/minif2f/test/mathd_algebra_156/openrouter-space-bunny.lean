import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have hx : x ^ 4 = 5 * x ^ 2 - 6 := by
    calc
      x ^ 4 = f x := (h₀ x).symm
      _ = g x := h₂
      _ = 5 * x ^ 2 - 6 := h₁ x
  have hy : y ^ 4 = 5 * y ^ 2 - 6 := by
    calc
      y ^ 4 = f y := (h₀ y).symm
      _ = g y := h₃
      _ = 5 * y ^ 2 - 6 := h₁ y
  have hx' : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    calc
      (x ^ 2 - 2) * (x ^ 2 - 3) = x ^ 4 - 5 * x ^ 2 + 6 := by ring
      _ = 0 := by nlinarith [hx]
  have hy' : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    calc
      (y ^ 2 - 2) * (y ^ 2 - 3) = y ^ 4 - 5 * y ^ 2 + 6 := by ring
      _ = 0 := by nlinarith [hy]
  have hx_cases : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    rcases mul_eq_zero.mp hx' with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hy_cases : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    rcases mul_eq_zero.mp hy' with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hx_cases with hx2 | hx3
  · rcases hy_cases with hy2 | hy3
    · nlinarith [h₄]
    · nlinarith [h₄]
  · rcases hy_cases with hy2 | hy3
    · nlinarith [h₄]
    · nlinarith [h₄]
