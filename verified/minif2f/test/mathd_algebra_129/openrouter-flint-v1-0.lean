import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $\dfrac{8^{-1}}{4^{-1}}-a^{-1}=1$. -/
theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
  have h₂ : (8:ℝ)⁻¹ / (4:ℝ)⁻¹ = (1:ℝ)/2 := by norm_num
  have h₃ : (1:ℝ)/2 - a⁻¹ = 1 := by
    simpa [h₂] using h₁
  have h₄ : -a⁻¹ = 1/2 := by linarith
  have h₅ : a⁻¹ = -1/2 := by linarith
  have h₆ : a = -2 := by
    have hmul : a * a⁻¹ = 1 := mul_inv_cancel₀ h₀
    have h₇ : a * (-1/2) = 1 := by
      rw [← h₅]
      exact hmul
    have h₈ : a = -2 := by
      calc
        a = a * (-1/2) * (-2) := by ring
        _ = -2 := by
          rw [h₇]
          norm_num
    exact h₈
  exact h₆
