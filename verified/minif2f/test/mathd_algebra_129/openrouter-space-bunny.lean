import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $\dfrac{8^{-1}}{4^{-1}}-a^{-1}=1$. -/
theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
  have hcalc : 8⁻¹ / 4⁻¹ = (1 / 2 : ℝ) := by
    norm_num
  rw [hcalc] at h₁
  field_simp [h₀] at h₁
  linarith
