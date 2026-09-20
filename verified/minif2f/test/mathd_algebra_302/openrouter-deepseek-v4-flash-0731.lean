import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\left(\frac{i}{2}\right)^2$. -/
theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by
  calc
    (Complex.I / 2) ^ 2 = Complex.I ^ 2 / (2:ℂ) ^ 2 := by ring
    _ = -(1 / 4 : ℂ) := by
      rw [Complex.I_sq]
      norm_num
