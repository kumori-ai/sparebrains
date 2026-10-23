import Mathlib

open scoped Nat
open scoped Real

/-- If $a = 8$, what is the value of $\left(16\sqrt[3]{a^2}\right)^{\frac 13}$? -/
theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  rw [h₀]
  have h₁ : (16 : ℝ) * (8 ^ 2 : ℝ) ^ ((1 : ℝ) / 3) > 0 := by norm_num
  have h₂ : (8 : ℝ) ^ 2 = 64 := by norm_num
  rw [h₂]
  have h₃ : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by
    norm_num [Real.rpow_def_of_pos]
    <;> linarith
  rw [h₃]
  have h₄ : (16 : ℝ) * 4 = 64 := by norm_num
  rw [h₄]
  have h₅ : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by
    norm_num [Real.rpow_def_of_pos]
    <;> linarith
  rw [h₅]
