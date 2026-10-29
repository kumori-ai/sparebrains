import Mathlib

open scoped Nat
open scoped Real

/--
A rectangular patio has an area of $180$ square feet and a perimeter of $54$ feet. What is the length of the diagonal (in feet) squared? -/
theorem mathd_algebra_141 (a b : ℝ) (h₁ : a * b = 180) (h₂ : 2 * (a + b) = 54) :
    a ^ 2 + b ^ 2 = 369 := by
  have hsum : a + b = 27 := by nlinarith
  have hsumsq : (a + b) ^ 2 = 729 := by
    rw [hsum]
    norm_num
  have hsq : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by
    ring
  have hfinal : a ^ 2 + b ^ 2 = 369 := by
    rw [hsq]
    rw [hsumsq]
    rw [h₁]
    norm_num
  exact hfinal
