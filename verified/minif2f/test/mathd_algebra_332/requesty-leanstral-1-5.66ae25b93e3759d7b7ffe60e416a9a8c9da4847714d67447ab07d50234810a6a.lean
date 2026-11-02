import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have h_sum : x + y = 14 := by
    linarith
  have h_sqrt19_pos : 0 < Real.sqrt (19 : ℝ) := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 19)
  have hxy_nonneg : 0 ≤ x * y := by
    by_contra! h_neg
    have h_neg' : x * y ≤ 0 := le_of_lt h_neg
    have h_sqrt_zero : Real.sqrt (x * y) = 0 := Real.sqrt_eq_zero_of_nonpos h_neg'
    rw [h_sqrt_zero] at h₁
    have : Real.sqrt (19 : ℝ) > 0 := h_sqrt19_pos
    linarith
  have hxy_eq : x * y = 19 := by
    calc
      x * y = (Real.sqrt (x * y)) ^ 2 := by rw [Real.sq_sqrt hxy_nonneg]
      _ = (Real.sqrt 19) ^ 2 := by rw [h₁]
      _ = 19 := by rw [Real.sq_sqrt (show 0 ≤ (19 : ℝ) from by norm_num)]
  calc
    x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    _ = 14 ^ 2 - 2 * 19 := by rw [h_sum, hxy_eq]
    _ = 158 := by norm_num
