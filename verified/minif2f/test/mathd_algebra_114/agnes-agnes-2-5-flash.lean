import Mathlib

open scoped Nat
open scoped Real

/-- If $a = 8$, what is the value of $\left(16\sqrt[3]{a^2}\right)^{\frac 13}$? -/
theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  subst h₀
  have h₁ : (8 : ℝ) ^ 2 = 64 := by norm_num
  have h₂ : ((8 : ℝ) ^ 2) ^ ((1 : ℝ) / 3) = 4 := by
    norm_num [Real.rpow_def_of_pos, Real.log_pow]
    <;> ring_nf
    <;> norm_num
  have h₃ : (16 : ℝ) * 4 = 64 := by norm_num
  have h₄ : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by
    norm_num [Real.rpow_def_of_pos, Real.log_pow]
    <;> ring_nf
    <;> norm_num
  calc
    (16 * ((8 : ℝ) ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3)
      = (16 * 4) ^ ((1 : ℝ) / 3) := by rw [h₂]
    _ = 64 ^ ((1 : ℝ) / 3) := by norm_num
    _ = 4 := by rw [h₄]
