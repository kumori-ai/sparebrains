import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $\dfrac{8^{-1}}{4^{-1}}-a^{-1}=1$. -/
theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
  have h₂ : (8 : ℝ)⁻¹ / (4 : ℝ)⁻¹ = 1/2 := by norm_num
  rw [h₂] at h₁
  have h₃ : a⁻¹ = -1/2 := by linarith
  field_simp [h₀] at h₃
  linarith
