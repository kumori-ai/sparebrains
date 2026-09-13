import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have hxy_pos : 0 < x * y := by
    have : 0 < Real.sqrt (x * y) := by
      rw [h₁]
      exact Real.sqrt_pos.mpr (by norm_num)
    exact Real.sqrt_pos.mp this
  have hxy : x * y = 19 := by
    have h : (Real.sqrt (x * y)) ^ 2 = (Real.sqrt 19) ^ 2 := by
      rw [h₁]
    rw [Real.sq_sqrt (le_of_lt hxy_pos), Real.sq_sqrt (by norm_num)] at h
    exact h
  have hsum : x + y = 14 := by linarith
  calc
    x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    _ = 14 ^ 2 - 2 * 19 := by rw [hsum, hxy]
    _ = 158 := by norm_num
