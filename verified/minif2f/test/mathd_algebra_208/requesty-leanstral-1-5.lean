import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $\sqrt{1,\!000,\!000} - \sqrt[3]{1,\!000,\!000}$? -/
theorem mathd_algebra_208 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by
  have hsqrt : Real.sqrt (1000000 : ℝ) = (1000 : ℝ) := by
    calc
      Real.sqrt (1000000 : ℝ) = Real.sqrt ((1000 : ℝ) ^ 2) := by norm_num
      _ = 1000 := Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1000)
  have hcube : (1000000 : ℝ) ^ ((1 : ℝ) / 3) = (100 : ℝ) := by
    have h100cube : (100 : ℝ) ^ (3 : ℝ) = (1000000 : ℝ) := by
      calc
        (100 : ℝ) ^ (3 : ℝ) = ((100 : ℝ) ^ (3 : ℕ) : ℝ) := by
          simpa using Real.rpow_natCast (100 : ℝ) 3
        _ = (100 ^ 3 : ℝ) := by norm_num
        _ = (1000000 : ℝ) := by norm_num
    calc
      (1000000 : ℝ) ^ ((1 : ℝ) / 3) = ((100 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by rw [h100cube]
      _ = (100 : ℝ) ^ ((3 : ℝ) * ((1 : ℝ) / 3)) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100) (3 : ℝ) ((1 : ℝ) / 3)]
      _ = (100 : ℝ) ^ (1 : ℝ) := by norm_num
      _ = (100 : ℝ) := by simp
  calc
    Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = (1000 : ℝ) - 1000000 ^ ((1 : ℝ) / 3) := by rw [hsqrt]
    _ = (1000 : ℝ) - (100 : ℝ) := by rw [hcube]
    _ = 900 := by norm_num
