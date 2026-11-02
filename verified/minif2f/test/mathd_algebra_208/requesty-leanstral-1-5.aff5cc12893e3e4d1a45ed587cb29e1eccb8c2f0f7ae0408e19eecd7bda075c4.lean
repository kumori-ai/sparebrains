import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $\sqrt{1,\!000,\!000} - \sqrt[3]{1,\!000,\!000}$? -/
theorem mathd_algebra_208 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by
  have h_cuberoot : (1000000 : ℝ) ^ ((1 : ℝ) / 3) = (100 : ℝ) := by
    have h_base : (1000000 : ℝ) = (100 : ℝ) ^ (3 : ℝ) := by norm_num
    rw [h_base]
    calc
      ((100 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (100 : ℝ) ^ ((3 : ℝ) * ((1 : ℝ) / 3)) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100) (3 : ℝ) ((1 : ℝ) / 3)]
      _ = (100 : ℝ) ^ (1 : ℝ) := by norm_num
      _ = (100 : ℝ) := by norm_num
  calc
    Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 1000 - 1000000 ^ ((1 : ℝ) / 3) := by norm_num
    _ = 1000 - 100 := by rw [h_cuberoot]
    _ = 900 := by norm_num
