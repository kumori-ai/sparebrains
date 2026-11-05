import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have h_sum : x + y = 14 := by linarith [h₀]
  have h_prod : x * y = 19 := by
    have h_nonneg : 0 ≤ x * y := by
      by_contra h_neg
      have : x * y < 0 := by linarith
      have : Real.sqrt (x * y) = 0 := by
        rw [Real.sqrt_eq_zero_of_nonpos]
        linarith
      rw [this] at h₁
      have : Real.sqrt 19 > 0 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    have h_sq_left : (Real.sqrt (x * y)) ^ 2 = x * y := by
      rw [Real.sq_sqrt]
      exact h_nonneg
    have h_sq_right : (Real.sqrt 19) ^ 2 = 19 := by
      rw [Real.sq_sqrt]
      norm_num
    have h_sq : (Real.sqrt (x * y)) ^ 2 = (Real.sqrt 19) ^ 2 := by rw [h₁]
    linarith
  calc
    x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    _ = 14 ^ 2 - 2 * 19 := by rw [h_sum, h_prod]
    _ = 158 := by norm_num
