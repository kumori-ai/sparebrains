import Mathlib

open scoped Nat
open scoped Real

/--
A rectangular patio has an area of $180$ square feet and a perimeter of $54$ feet. What is the length of the diagonal (in feet) squared? -/
theorem mathd_algebra_141 (a b : ℝ) (h₁ : a * b = 180) (h₂ : 2 * (a + b) = 54) :
    a ^ 2 + b ^ 2 = 369 := by
  have hsum : a + b = 27 := by linarith
  have hsq : (a + b) ^ 2 = 729 := by
    rw [hsum]
    norm_num
  have hsq' : a ^ 2 + 2 * a * b + b ^ 2 = 729 := by
    calc
      a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2 := by ring
      _ = 729 := by
        rw [hsum]
        norm_num
  nlinarith [h₁, hsq']
