import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have h₅ : x ^ 4 - 5 * x ^ 2 + 6 = 0 := by
    have h₅a : x ^ 4 - 5 * x ^ 2 + 6 = f x - g x := by
      rw [h₀, h₁]
      <;> ring
    rw [h₅a]
    rw [h₂]
    ring
  have h₆ : y ^ 4 - 5 * y ^ 2 + 6 = 0 := by
    have h₆a : y ^ 4 - 5 * y ^ 2 + 6 = f y - g y := by
      rw [h₀, h₁]
      <;> ring
    rw [h₆a]
    rw [h₃]
    ring
  have h₇ : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    have h₇a : x ^ 4 - 5 * x ^ 2 + 6 = (x ^ 2 - 2) * (x ^ 2 - 3) := by ring
    rw [h₇a] at h₅
    exact h₅
  have h₈ : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    have h₈a : y ^ 4 - 5 * y ^ 2 + 6 = (y ^ 2 - 2) * (y ^ 2 - 3) := by ring
    rw [h₈a] at h₆
    exact h₆
  have h₉ : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    simpa [sub_eq_zero] using h₇
  have h₁₀ : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    simpa [sub_eq_zero] using h₈
  cases h₉ with
  | inl h₉ =>
    cases h₁₀ with
    | inl h₁₀ =>
      have : (2 : ℝ) < 2 := by simpa [h₉, h₁₀] using h₄
      linarith
    | inr h₁₀ =>
      simp [h₉, h₁₀]
      <;> norm_num
  | inr h₉ =>
    cases h₁₀ with
    | inl h₁₀ =>
      have : (3 : ℝ) < 2 := by simpa [h₉, h₁₀] using h₄
      linarith
    | inr h₁₀ =>
      have : (3 : ℝ) < 3 := by simpa [h₉, h₁₀] using h₄
      linarith
