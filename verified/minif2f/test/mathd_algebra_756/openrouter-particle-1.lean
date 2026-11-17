import Mathlib

open scoped Nat
open scoped Real

/-- Given $2^a = 32$ and $a^b = 125$ find $b^a$. -/
theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) by norm_num]
    rw [Real.log_pow]
    norm_num
  have ha : a = 5 := by
    have h : a * Real.log 2 = 5 * Real.log 2 := by
      calc
        a * Real.log 2 = Real.log ((2 : ℝ) ^ a) := by
          rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
        _ = Real.log 32 := by rw [h₀]
        _ = 5 * Real.log 2 := hlog32
    exact mul_right_cancel₀ (ne_of_gt hlog2pos) h
  have hlog5pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hlog125 : Real.log 125 = 3 * Real.log 5 := by
    rw [show (125 : ℝ) = (5 : ℝ) ^ (3 : ℕ) by norm_num]
    rw [Real.log_pow]
    norm_num
  have hb : b = 3 := by
    have h : b * Real.log 5 = 3 * Real.log 5 := by
      calc
        b * Real.log 5 = Real.log ((5 : ℝ) ^ b) := by
          rw [Real.log_rpow (by norm_num : (0 : ℝ) < 5)]
        _ = Real.log 125 := by
          rw [ha] at h₁
          rw [h₁]
        _ = 3 * Real.log 5 := hlog125
    exact mul_right_cancel₀ (ne_of_gt hlog5pos) h
  rw [ha, hb]
  rw [show (5 : ℝ) = ((5 : Nat) : ℝ) by norm_num]
  rw [Real.rpow_natCast]
  norm_num
