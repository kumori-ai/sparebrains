import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $\dfrac{8^{-1}}{4^{-1}}-a^{-1}=1$. -/
theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
  have h2 : (8 : ℝ)⁻¹ / (4 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [h2] at h₁
  have h3 : a⁻¹ = -1 / 2 := by linarith
  have h4 : a = (-1 / 2 : ℝ)⁻¹ := by
    rw [← h3, inv_inv]
  norm_num at h4
  exact h4
