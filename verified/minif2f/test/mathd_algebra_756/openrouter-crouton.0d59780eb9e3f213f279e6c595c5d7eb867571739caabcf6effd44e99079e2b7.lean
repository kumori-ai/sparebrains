import Mathlib

open scoped Nat
open scoped Real

/-- Given $2^a = 32$ and $a^b = 125$ find $b^a$. -/
theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog5 : Real.log 5 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have ha : a = 5 := by
    have h := congrArg Real.log h₀
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at h
    have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
      have e : (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      rw [e, Real.log_pow]
      norm_num
    rw [h32] at h
    exact mul_right_cancel₀ hlog2 h
  have hb : b = 3 := by
    rw [ha] at h₁
    have h := congrArg Real.log h₁
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 5)] at h
    have h125 : Real.log (125 : ℝ) = 3 * Real.log 5 := by
      have e : (125 : ℝ) = (5 : ℝ) ^ (3 : ℕ) := by norm_num
      rw [e, Real.log_pow]
      norm_num
    rw [h125] at h
    exact mul_right_cancel₀ hlog5 h
  rw [ha, hb]
  have e : (5 : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
  rw [e, Real.rpow_natCast]
  norm_num
