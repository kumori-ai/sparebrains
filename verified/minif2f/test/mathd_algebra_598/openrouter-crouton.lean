import Mathlib

open scoped Nat
open scoped Real

/--
Suppose that  $4^{a}=5$, $5^{b}=6$, $6^{c}=7,$ and  $7^{d}=8$. What is $a\cdot b\cdot c\cdot d$? -/
theorem mathd_algebra_598 (a b c d : ℝ) (h₁ : (4 : ℝ) ^ a = 5) (h₂ : (5 : ℝ) ^ b = 6)
    (h₃ : (6 : ℝ) ^ c = 7) (h₄ : (7 : ℝ) ^ d = 8) : a * b * c * d = 3 / 2 := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlog7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have ha : a * Real.log 4 = Real.log 5 := by
    have h := congrArg Real.log h₁
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 4)] at h
    exact h
  have hb : b * Real.log 5 = Real.log 6 := by
    have h := congrArg Real.log h₂
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 5)] at h
    exact h
  have hc : c * Real.log 6 = Real.log 7 := by
    have h := congrArg Real.log h₃
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 6)] at h
    exact h
  have hd : d * Real.log 7 = Real.log 8 := by
    have h := congrArg Real.log h₄
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 7)] at h
    exact h
  have ha_eq : a = Real.log 5 / Real.log 4 := by
    rw [eq_div_iff (ne_of_gt hlog4)]
    exact ha
  have hb_eq : b = Real.log 6 / Real.log 5 := by
    rw [eq_div_iff (ne_of_gt hlog5)]
    exact hb
  have hc_eq : c = Real.log 7 / Real.log 6 := by
    rw [eq_div_iff (ne_of_gt hlog6)]
    exact hc
  have hd_eq : d = Real.log 8 / Real.log 7 := by
    rw [eq_div_iff (ne_of_gt hlog7)]
    exact hd
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    have e8 : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
    rw [e8, Real.log_pow]
    norm_num
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    have e4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [e4, Real.log_pow]
    norm_num
  have hlog8_eq : Real.log 8 = 3 / 2 * Real.log 4 := by
    rw [l8, l4]
    ring
  rw [ha_eq, hb_eq, hc_eq, hd_eq, hlog8_eq]
  field_simp [ne_of_gt hlog4, ne_of_gt hlog5, ne_of_gt hlog6, ne_of_gt hlog7]
