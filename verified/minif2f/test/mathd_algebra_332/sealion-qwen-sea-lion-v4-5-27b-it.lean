import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have h_sum : x + y = 14 := by linarith
  have h_prod : x * y = 19 := by
    have h₂ : 0 ≤ (19 : ℝ) := by norm_num
    have h₃ : 0 < Real.sqrt (x * y) := by simpa [h₁] using Real.sqrt_pos.mpr (by norm_num)
    have h₄ : 0 < x * y := Real.sqrt_pos.mp h₃
    have h₅ : 0 ≤ x * y := by linarith
    rw [Real.sqrt_inj h₅ h₂] at h₁
    exact h₁
  have h_sq : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
  rw [h_sq, h_sum, h_prod]
  norm_num
