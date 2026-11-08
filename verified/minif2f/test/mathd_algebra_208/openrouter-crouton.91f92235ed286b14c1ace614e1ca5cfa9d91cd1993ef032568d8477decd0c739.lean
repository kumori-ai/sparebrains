import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $\sqrt{1,\!000,\!000} - \sqrt[3]{1,\!000,\!000}$? -/
theorem mathd_algebra_208 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by
  have hsqrt : Real.sqrt 1000000 = 1000 := by
    have h : (1000000 : ℝ) = (1000 : ℝ) ^ 2 := by norm_num
    rw [h, Real.sqrt_sq (by norm_num)]
  have hcube : (1000000 : ℝ) ^ ((1 : ℝ) / 3) = 100 := by
    have h : (1000000 : ℝ) = (100 : ℝ) ^ 3 := by norm_num
    rw [h, ← Real.rpow_natCast (100 : ℝ) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100)]
    have hexp : ((3 : ℕ) : ℝ) * (1 / 3) = 1 := by norm_num
    rw [hexp, Real.rpow_one]
  rw [hsqrt, hcube]
  norm_num
