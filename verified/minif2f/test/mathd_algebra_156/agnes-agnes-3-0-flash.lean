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
  have h_eq : x ^ 4 - 5 * x ^ 2 + 6 = 0 := by
    linarith [hx]
  have h_eq2 : y ^ 4 - 5 * y ^ 2 + 6 = 0 := by
    linarith [hy]
  have h_a : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    have h : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
      ring_nf at h_eq
      nlinarith
    have h_cases : (x ^ 2 - 2 = 0 ∨ x ^ 2 - 3 = 0) := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h
    cases h_cases with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  have h_b : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    have h : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
      ring_nf at h_eq2
      nlinarith
    have h_cases : (y ^ 2 - 2 = 0 ∨ y ^ 2 - 3 = 0) := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h
    cases h_cases with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  cases h_a with
  | inl h_x2 =>
    cases h_b with
    | inl h_y2 =>
      exfalso
      have h_contra : ¬ x ^ 2 < y ^ 2 := by
        rw [h_x2, h_y2]
        linarith
      exact h_contra h₄
    | inr h_y2 =>
      have h_diff : y ^ 2 - x ^ 2 = 1 := by
        rw [h_x2, h_y2]
        norm_num
      exact h_diff
  | inr h_x2 =>
    cases h_b with
    | inl h_y2 =>
      exfalso
      have h_contra : ¬ x ^ 2 < y ^ 2 := by
        rw [h_x2, h_y2]
        linarith
      exact h_contra h₄
    | inr h_y2 =>
      exfalso
      have h_contra : ¬ x ^ 2 < y ^ 2 := by
        rw [h_x2, h_y2]
        linarith
      exact h_contra h₄
