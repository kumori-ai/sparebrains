import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\left(\frac{i}{2}\right)^2$. -/
theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by
  calc
    (Complex.I / 2) ^ 2 = (Complex.I / 2) * (Complex.I / 2) := by rw [pow_two]
    _ = Complex.I * Complex.I / 4 := by
      field_simp
      ring
    _ = (-1 : ℂ) / 4 := by rw [Complex.I_mul_I]
    _ = -(1 / 4) := by norm_num
