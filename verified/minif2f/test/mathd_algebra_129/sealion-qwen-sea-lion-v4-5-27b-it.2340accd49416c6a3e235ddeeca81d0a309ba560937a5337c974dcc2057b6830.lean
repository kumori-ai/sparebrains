import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $\dfrac{8^{-1}}{4^{-1}}-a^{-1}=1$. -/
theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
  have h₂ : (1/2 : ℝ) - a⁻¹ = 1 := by
    norm_num at h₁ ⊢
    <;> simpa using h₁
  field_simp [h₀] at h₂ ⊢
  ring_nf at h₂ ⊢
  linarith
