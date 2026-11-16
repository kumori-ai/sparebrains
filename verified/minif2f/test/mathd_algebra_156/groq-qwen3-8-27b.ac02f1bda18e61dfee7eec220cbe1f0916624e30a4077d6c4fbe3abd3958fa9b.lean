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
  have hx' : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    have h : x ^ 4 - 5 * x ^ 2 + 6 = 0 := by linarith
    have h2 : (x ^ 2 - 2) * (x ^ 2 - 3) = x ^ 4 - 5 * x ^ 2 + 6 := by ring
    linarith
  have hy' : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    have h : y ^ 4 - 5 * y ^ 2 + 6 = 0 := by linarith
    have h2 : (y ^ 2 - 2) * (y ^ 2 - 3) = y ^ 4 - 5 * y ^ 2 + 6 := by ring
    linarith
  have hx_cases : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    have h1 : x ^ 2 - 2 = 0 ∨ x ^ 2 - 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero at hx'
      exact hx'
    cases h1 with
    | inl h1 => exact Or.inl (by linarith)
    | inr h1 => exact Or.inr (by linarith)
  have hy_cases : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    have h1 : y ^ 2 - 2 = 0 ∨ y ^ 2 - 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero at hy'
      exact hy'
    cases h1 with
    | inl h1 => exact Or.inl (by linarith)
    | inr h1 => exact Or.inr (by linarith)
  cases hx_cases with
  | inl hx2 =>
    cases hy_cases with
    | inl hy2 =>
      linarith
    | inr hy3 =>
      linarith
  | inr hx3 =>
    cases hy_cases with
    | inl hy2 =>
      linarith
    | inr hy3 =>
      linarith
