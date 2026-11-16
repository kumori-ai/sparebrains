import Mathlib

open scoped Nat
open scoped Real

/--
Suppose that  $4^{a}=5$, $5^{b}=6$, $6^{c}=7,$ and  $7^{d}=8$. What is $a\cdot b\cdot c\cdot d$? -/
theorem mathd_algebra_598 (a b c d : ℝ) (h₁ : (4 : ℝ) ^ a = 5) (h₂ : (5 : ℝ) ^ b = 6)
    (h₃ : (6 : ℝ) ^ c = 7) (h₄ : (7 : ℝ) ^ d = 8) : a * b * c * d = 3 / 2 := by
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have h5pos : (0 : ℝ) < 5 := by norm_num
  have h6pos : (0 : ℝ) < 6 := by norm_num
  have h7pos : (0 : ℝ) < 7 := by norm_num
  have h4ne : Real.log (4 : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))
  have h5ne : Real.log (5 : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))
  have h6ne : Real.log (6 : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))
  have h7ne : Real.log (7 : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))
  have ha : a = Real.log 5 / Real.log 4 := by
    have h := congrArg Real.log h₁
    rw [Real.log_rpow h4pos] at h
    rw [eq_div_iff h4ne]
    exact h
  have hb : b = Real.log 6 / Real.log 5 := by
    have h := congrArg Real.log h₂
    rw [Real.log_rpow h5pos] at h
    rw [eq_div_iff h5ne]
    exact h
  have hc : c = Real.log 7 / Real.log 6 := by
    have h := congrArg Real.log h₃
    rw [Real.log_rpow h6pos] at h
    rw [eq_div_iff h6ne]
    exact h
  have hd : d = Real.log 8 / Real.log 7 := by
    have h := congrArg Real.log h₄
    rw [Real.log_rpow h7pos] at h
    rw [eq_div_iff h7ne]
    exact h
  have hlog8 : Real.log (8 : ℝ) = (3 / 2) * Real.log (4 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [Real.log_pow, Real.log_pow]
    ring
  rw [ha, hb, hc, hd, hlog8]
  field_simp [h4ne, h5ne, h6ne, h7ne]
