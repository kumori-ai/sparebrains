import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $\dfrac{8^{-1}}{4^{-1}}-a^{-1}=1$. -/
theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
  have h₂ : (8⁻¹ / 4⁻¹ : ℝ) = 1 / 2 := by norm_num
  rw [h₂] at h₁
  have h₃ : a⁻¹ = -1 / 2 := by linarith
  have h₄ : a * a⁻¹ = a * (-1 / 2) := by rw [h₃]
  rw [mul_inv_cancel₀ h₀] at h₄
  -- h₄ : 1 = a * (-1 / 2)
  nlinarith
