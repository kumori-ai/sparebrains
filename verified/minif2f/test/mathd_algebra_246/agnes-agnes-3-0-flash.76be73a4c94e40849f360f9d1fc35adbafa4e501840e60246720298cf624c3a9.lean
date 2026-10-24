import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h₃ : f 3 = 8 := by
    have h₄ : f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 := by
      rw [h₀]
      <;> norm_num
    have h₅ : f (-3) = a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 := by
      rw [h₀]
      <;> norm_num
    have h₆ : a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 = 2 := by
      rw [h₅] at h₂
      exact h₂
    have h₇ : a * (-3) ^ 4 = a * 3 ^ 4 := by
      ring_nf
      <;> norm_num
    have h₈ : b * (-3) ^ 2 = b * 3 ^ 2 := by
      ring_nf
      <;> norm_num
    have h₉ : a * 3 ^ 4 - b * 3 ^ 2 + (-3) + 5 = 2 := by
      linarith [h₇, h₈]
    have h₁₀ : a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 = 8 := by
      have h₁₁ : a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 = (a * 3 ^ 4 - b * 3 ^ 2 + (-3) + 5) + 6 := by
        ring_nf
        <;> norm_num
      rw [h₁₁]
      linarith [h₉]
    rw [h₄]
    exact h₁₀
  exact h₃
