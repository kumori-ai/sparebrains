import Mathlib

open scoped Nat
open scoped Real

/-- If $a = 8$, what is the value of $\left(16\sqrt[3]{a^2}\right)^{\frac 13}$? -/
theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  rw [h₀]
  have h64_cuberoot : (64 : ℝ) ^ ((1 : ℝ)/3) = 4 := by
    calc
      (64 : ℝ) ^ ((1 : ℝ)/3) = ((4 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ)/3) := by norm_num
      _ = ((4 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ)/3) := by norm_num
      _ = (4 : ℝ) ^ ((3 : ℝ) * ((1 : ℝ)/3)) := by rw [Real.rpow_mul (show (4 : ℝ) ≥ 0 from by norm_num) (3 : ℝ) ((1 : ℝ)/3)]
      _ = (4 : ℝ) ^ (1 : ℝ) := by norm_num
      _ = 4 := by norm_num
  calc
    (16 * ((8 : ℝ) ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = (16 * (64 : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) := by norm_num
    _ = (16 * 4) ^ ((1 : ℝ) / 3) := by rw [h64_cuberoot]
    _ = (64 : ℝ) ^ ((1 : ℝ) / 3) := by norm_num
    _ = 4 := by rw [h64_cuberoot]
