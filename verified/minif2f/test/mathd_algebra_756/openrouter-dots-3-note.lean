import Mathlib

open scoped Nat
open scoped Real

/-- Given $2^a = 32$ and $a^b = 125$ find $b^a$. -/
theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := by
    apply Real.log_pos
    norm_num
  have hlog2ne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2pos
  have hlog5pos : 0 < Real.log (5 : ℝ) := by
    apply Real.log_pos
    norm_num
  have hlog5ne : Real.log (5 : ℝ) ≠ 0 := ne_of_gt hlog5pos
  have h2pow5 : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num
  have h5pow3 : (5 : ℝ) ^ (3 : ℝ) = 125 := by norm_num
  have ha : a = 5 := by
    have h_eq : a * Real.log (2 : ℝ) = (5 : ℝ) * Real.log (2 : ℝ) := by
      calc
        a * Real.log (2 : ℝ) = Real.log ((2 : ℝ) ^ a) := (Real.log_rpow (x := (2 : ℝ)) (by norm_num : 0 < (2 : ℝ)) a).symm
        _ = Real.log (32 : ℝ) := by rw [h₀]
        _ = Real.log ((2 : ℝ) ^ (5 : ℝ)) := by rw [h2pow5]
        _ = (5 : ℝ) * Real.log (2 : ℝ) := Real.log_rpow (x := (2 : ℝ)) (by norm_num : 0 < (2 : ℝ)) (5 : ℝ)
    exact mul_right_cancel₀ hlog2ne h_eq
  have hb : b = 3 := by
    rw [ha] at h₁
    have h_eq : b * Real.log (5 : ℝ) = (3 : ℝ) * Real.log (5 : ℝ) := by
      calc
        b * Real.log (5 : ℝ) = Real.log ((5 : ℝ) ^ b) := (Real.log_rpow (x := (5 : ℝ)) (by norm_num : 0 < (5 : ℝ)) b).symm
        _ = Real.log (125 : ℝ) := by rw [h₁]
        _ = Real.log ((5 : ℝ) ^ (3 : ℝ)) := by rw [h5pow3]
        _ = (3 : ℝ) * Real.log (5 : ℝ) := Real.log_rpow (x := (5 : ℝ)) (by norm_num : 0 < (5 : ℝ)) (3 : ℝ)
    exact mul_right_cancel₀ hlog5ne h_eq
  rw [ha, hb]
  norm_num
