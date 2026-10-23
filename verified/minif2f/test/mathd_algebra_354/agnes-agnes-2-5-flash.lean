import Mathlib

open scoped Nat
open scoped Real

/--
In an arithmetic sequence, the 7th term is 30, and the 11th term is 60. What is the 21st term of this sequence? -/
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  have h₂ : d = 15 / 2 := by
    have h₂' : 4 * d = 30 := by linarith
    linarith
  have h₃ : a = -15 := by
    have h₃' : a + 6 * (15 / 2) = 30 := by rw [h₂] at h₀; exact h₀
    linarith
  rw [h₃, h₂]
  norm_num
