import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have h₂ : x + y = 14 := by
    field_simp at h₀
    linarith
  have h₃ : 0 ≤ x * y := by
    have h₃' : 0 < Real.sqrt (x * y) := by
      rw [h₁]
      exact Real.sqrt_pos.mpr (by norm_num)
    exact le_of_lt (Real.sqrt_pos.mp h₃')
  have h₄ : x * y = 19 := by
    have : Real.sqrt (x * y) = Real.sqrt 19 ↔ x * y = 19 := Real.sqrt_inj h₃ (by norm_num)
    exact this.mp h₁
  calc
    x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    _ = 14 ^ 2 - 2 * 19 := by rw [h₂, h₄]
    _ = 158 := by norm_num
