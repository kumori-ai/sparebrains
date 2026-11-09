import Mathlib

open scoped Nat
open scoped Real

/-- If $a = 8$, what is the value of $\left(16\sqrt[3]{a^2}\right)^{\frac 13}$? -/
theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  have h64 : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by
    calc (64 : ℝ) ^ ((1 : ℝ) / 3) = ((4 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) := by
          rw [show (64 : ℝ) = (4 : ℝ) ^ 3 by norm_num]
      _ = ((4 : ℝ) ^ (((3 : ℕ) : ℝ))) ^ ((1 : ℝ) / 3) := by
          rw [← Real.rpow_natCast]
      _ = (4 : ℝ) ^ ((((3 : ℕ) : ℝ)) * ((1 : ℝ) / 3)) := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = (4 : ℝ) ^ ((1 : ℝ)) := by
          congr 1
          norm_num
      _ = 4 := by rw [Real.rpow_one]
  have h_inner : ((8 : ℝ) ^ 2) ^ ((1 : ℝ) / 3) = 4 := by
    have h : (8 : ℝ) ^ 2 = 64 := by norm_num
    rw [h]
    exact h64
  rw [h₀, h_inner]
  have h : (16 : ℝ) * 4 = 64 := by norm_num
  rw [h]
  exact h64
