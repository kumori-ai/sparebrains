import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $\dfrac{8^{-1}}{4^{-1}}-a^{-1}=1$. -/
theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
   norm_num at h₁
   have h₂ : a⁻¹ = -1/2 := by linarith
   have h₃ : a * a⁻¹ = 1 := mul_inv_cancel₀ h₀
   rw [h₂] at h₃
   linarith
