import Mathlib

open scoped Nat
open scoped Real

/--
In an arithmetic sequence, the 7th term is 30, and the 11th term is 60. What is the 21st term of this sequence? -/
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  have h₂ : 4 * d = 30 := by
    linarith [h₀, h₁]
  have h₃ : d = 7.5 := by
    linarith [h₂]
  have h₄ : a = 30 - 6 * d := by
    linarith [h₀]
  rw [h₄, h₃]
  ring
