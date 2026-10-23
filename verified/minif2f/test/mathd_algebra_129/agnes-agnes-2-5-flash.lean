import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $\dfrac{8^{-1}}{4^{-1}}-a^{-1}=1$. -/
theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
  have h₂ : (8 : ℝ)⁻¹ / (4 : ℝ)⁻¹ = 1 / 2 := by norm_num
  have h₃ : (1 : ℝ) / 2 - a⁻¹ = 1 := by simpa [h₂] using h₁
  have h₄ : a⁻¹ = -1 / 2 := by linarith
  have h₅ : a = -2 := by
    have h₅₁ : a ≠ 0 := h₀
    have h₅₂ : (a : ℝ)⁻¹ = (-2 : ℝ)⁻¹ := by
      rw [h₄]
      norm_num
    have h₅₃ : a = -2 := by
      apply_fun (·⁻¹) at h₅₂
      simpa [inv_inv] using h₅₂
    exact h₅₃
  exact h₅
