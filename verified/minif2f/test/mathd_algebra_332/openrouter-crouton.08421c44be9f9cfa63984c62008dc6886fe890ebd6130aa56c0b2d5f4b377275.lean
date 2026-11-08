import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have hxy_pos : 0 < x * y := by
    have h19 : 0 < Real.sqrt 19 := Real.sqrt_pos_of_pos (by norm_num)
    have hpos : 0 < Real.sqrt (x * y) := by
      rw [h₁]
      exact h19
    exact Real.sqrt_pos.mp hpos
  have hxy : x * y = 19 := by
    have hsq : (Real.sqrt (x * y)) ^ 2 = (Real.sqrt 19) ^ 2 := by rw [h₁]
    rw [Real.sq_sqrt (le_of_lt hxy_pos), Real.sq_sqrt (by norm_num)] at hsq
    exact hsq
  have hsum : x + y = 14 := by linarith
  have h : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
  rw [h, hsum, hxy]
  norm_num
