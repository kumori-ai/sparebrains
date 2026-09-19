import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\left(\frac{i}{2}\right)^2$. -/
theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by
  field_simp
  have h : Complex.I ^ 2 = -1 := by
    exact Complex.I_sq
  rw [h]
  norm_num
