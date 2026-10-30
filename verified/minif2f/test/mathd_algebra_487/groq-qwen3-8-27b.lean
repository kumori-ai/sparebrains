import Mathlib

open scoped Nat
open scoped Real

/-- What is the distance between the two intersections of $y=x^2$ and $x+y=1$? -/
theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
  have h₅ : a ^ 2 + a - 1 = 0 := by
    nlinarith [h₀, h₁]
  have h₆ : c ^ 2 + c - 1 = 0 := by
    nlinarith [h₂, h₃]
  have h₇ : a + c = -1 := by
    have h₇₁ : a ^ 2 + a - 1 = 0 := h₅
    have h₇₂ : c ^ 2 + c - 1 = 0 := h₆
    have h₇₃ : a ^ 2 - c ^ 2 + (a - c) = 0 := by linarith
    have h₇₄ : (a - c) * (a + c + 1) = 0 := by
      nlinarith
    have h₇₅ : a + c + 1 = 0 := by
      apply mul_left_cancel₀ (sub_ne_zero.mpr h₄)
      nlinarith
    linarith
  have h₈ : a * c = -1 := by
    have h₈₁ : a ^ 2 + a - 1 = 0 := h₅
    have h₈₂ : c ^ 2 + c - 1 = 0 := h₆
    have h₈₃ : a + c = -1 := h₇
    nlinarith
  have h₉ : (a - c) ^ 2 = 5 := by
    nlinarith [h₇, h₈]
  have h₁₀ : (b - d) ^ 2 = 5 := by
    rw [h₀, h₂]
    have h₁₀₁ : (a ^ 2 - c ^ 2) ^ 2 = ((a - c) * (a + c)) ^ 2 := by ring
    have h₁₀₂ : ((a - c) * (a + c)) ^ 2 = (a - c) ^ 2 * (a + c) ^ 2 := by ring
    have h₁₀₃ : (a + c) ^ 2 = 1 := by nlinarith [h₇]
    have h₁₀₄ : (a - c) ^ 2 = 5 := h₉
    nlinarith [h₁₀₁, h₁₀₂, h₁₀₃, h₁₀₄]
  have h₁₁ : (a - c) ^ 2 + (b - d) ^ 2 = 10 := by
    nlinarith [h₉, h₁₀]
  rw [h₁₁]
