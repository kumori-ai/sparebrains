import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have h₅ : f x = x ^ 4 := h₀ x
  have h₆ : g x = 5 * x ^ 2 - 6 := h₁ x
  have h₇ : f y = y ^ 4 := h₀ y
  have h₈ : g y = 5 * y ^ 2 - 6 := h₁ y
  have h₉ : x ^ 4 = 5 * x ^ 2 - 6 := by
    calc
      x ^ 4 = f x := by symm; exact h₅
      _ = g x := h₂
      _ = 5 * x ^ 2 - 6 := h₆
  have h₁₀ : y ^ 4 = 5 * y ^ 2 - 6 := by
    calc
      y ^ 4 = f y := by symm; exact h₇
      _ = g y := h₃
      _ = 5 * y ^ 2 - 6 := h₈
  have h₁₁ : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    have h_eq : (x ^ 2) ^ 2 - 5 * (x ^ 2) + 6 = 0 := by
      nlinarith
    have h_factor : ((x ^ 2) - 2) * ((x ^ 2) - 3) = 0 := by
      nlinarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with h | h
    · left; linarith
    · right; linarith
  have h₁₂ : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    have h_eq : (y ^ 2) ^ 2 - 5 * (y ^ 2) + 6 = 0 := by
      nlinarith
    have h_factor : ((y ^ 2) - 2) * ((y ^ 2) - 3) = 0 := by
      nlinarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with h | h
    · left; linarith
    · right; linarith
  rcases h₁₁ with hx2 | hx3
  · -- x^2 = 2
    rcases h₁₂ with hy2 | hy3
    · -- y^2 = 2
      exfalso
      linarith [h₄, hx2, hy2]
    · -- y^2 = 3
      calc
        y ^ 2 - x ^ 2 = 3 - 2 := by rw [hy3, hx2]
        _ = 1 := by norm_num
  · -- x^2 = 3
    rcases h₁₂ with hy2 | hy3
    · -- y^2 = 2
      exfalso
      linarith [h₄, hx3, hy2]
    · -- y^2 = 3
      exfalso
      linarith [h₄, hx3, hy3]
