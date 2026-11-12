import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have h₅ : x ^ 4 = 5 * x ^ 2 - 6 := by
    rw [h₀, h₁] at h₂
    exact h₂
  have h₆ : y ^ 4 = 5 * y ^ 2 - 6 := by
    rw [h₀, h₁] at h₃
    exact h₃
  have h₇ : x ^ 4 - 5 * x ^ 2 + 6 = 0 := by linarith
  have h₈ : y ^ 4 - 5 * y ^ 2 + 6 = 0 := by linarith
  have h₉ : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    have : x ^ 4 - 5 * x ^ 2 + 6 = (x ^ 2 - 2) * (x ^ 2 - 3) := by ring
    rw [← this]
    exact h₇
  have h₁₀ : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    have : y ^ 4 - 5 * y ^ 2 + 6 = (y ^ 2 - 2) * (y ^ 2 - 3) := by ring
    rw [← this]
    exact h₈
  have h₁₁ : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    have : x ^ 2 - 2 = 0 ∨ x ^ 2 - 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h₉
    cases this with
    | inl h => exact Or.inl (by linarith)
    | inr h => exact Or.inr (by linarith)
  have h₁₂ : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    have : y ^ 2 - 2 = 0 ∨ y ^ 2 - 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h₁₀
    cases this with
    | inl h => exact Or.inl (by linarith)
    | inr h => exact Or.inr (by linarith)
  cases h₁₁ with
  | inl hx2 =>
    cases h₁₂ with
    | inl hy2 =>
      linarith
    | inr hy3 =>
      linarith
  | inr hx3 =>
    cases h₁₂ with
    | inl hy2 =>
      linarith
    | inr hy3 =>
      linarith
