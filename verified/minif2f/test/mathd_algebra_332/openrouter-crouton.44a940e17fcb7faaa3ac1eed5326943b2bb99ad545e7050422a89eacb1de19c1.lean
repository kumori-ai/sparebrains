import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have hxy_pos : 0 < x * y := by
    by_contra h
    push_neg at h
    have hsqrt0 : Real.sqrt (x * y) = 0 := Real.sqrt_eq_zero_of_nonpos h
    rw [h₁] at hsqrt0
    have hpos : (0 : ℝ) < Real.sqrt 19 := Real.sqrt_pos_of_pos (by norm_num)
    linarith
  have hxy : x * y = 19 := by
    have h2 : (Real.sqrt (x * y)) ^ 2 = (Real.sqrt 19) ^ 2 := by rw [h₁]
    rw [Real.sq_sqrt (le_of_lt hxy_pos), Real.sq_sqrt (by norm_num)] at h2
    exact h2
  have hsum : x + y = 14 := by linarith
  have h : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
  rw [h, hsum, hxy]
  norm_num
