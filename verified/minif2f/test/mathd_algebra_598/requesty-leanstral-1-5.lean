import Mathlib

open scoped Nat
open scoped Real

/--
Suppose that  $4^{a}=5$, $5^{b}=6$, $6^{c}=7,$ and  $7^{d}=8$. What is $a\cdot b\cdot c\cdot d$? -/
theorem mathd_algebra_598 (a b c d : ℝ) (h₁ : (4 : ℝ) ^ a = 5) (h₂ : (5 : ℝ) ^ b = 6)
    (h₃ : (6 : ℝ) ^ c = 7) (h₄ : (7 : ℝ) ^ d = 8) : a * b * c * d = 3 / 2 := by
  have h4pos : 0 < (4 : ℝ) := by norm_num
  have h5pos : 0 < (5 : ℝ) := by norm_num
  have h6pos : 0 < (6 : ℝ) := by norm_num
  have h7pos : 0 < (7 : ℝ) := by norm_num
  have h4gt1 : 1 < (4 : ℝ) := by norm_num
  have h5gt1 : 1 < (5 : ℝ) := by norm_num
  have h6gt1 : 1 < (6 : ℝ) := by norm_num
  have h7gt1 : 1 < (7 : ℝ) := by norm_num
  have h2gt1 : 1 < (2 : ℝ) := by norm_num
  have hlog4pos : 0 < Real.log (4 : ℝ) := Real.log_pos h4gt1
  have hlog5pos : 0 < Real.log (5 : ℝ) := Real.log_pos h5gt1
  have hlog6pos : 0 < Real.log (6 : ℝ) := Real.log_pos h6gt1
  have hlog7pos : 0 < Real.log (7 : ℝ) := Real.log_pos h7gt1
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos h2gt1
  have hlog4ne0 : Real.log (4 : ℝ) ≠ 0 := by linarith
  have hlog5ne0 : Real.log (5 : ℝ) ≠ 0 := by linarith
  have hlog6ne0 : Real.log (6 : ℝ) ≠ 0 := by linarith
  have hlog7ne0 : Real.log (7 : ℝ) ≠ 0 := by linarith
  have hlog2ne0 : Real.log (2 : ℝ) ≠ 0 := by linarith
  have ha : a = Real.log (5 : ℝ) / Real.log (4 : ℝ) := by
    apply (eq_div_iff_mul_eq hlog4ne0).mpr
    calc
      a * Real.log (4 : ℝ) = Real.log ((4 : ℝ) ^ a) := by rw [Real.log_rpow h4pos a]
      _ = Real.log (5 : ℝ) := by rw [h₁]
  have hb : b = Real.log (6 : ℝ) / Real.log (5 : ℝ) := by
    apply (eq_div_iff_mul_eq hlog5ne0).mpr
    calc
      b * Real.log (5 : ℝ) = Real.log ((5 : ℝ) ^ b) := by rw [Real.log_rpow h5pos b]
      _ = Real.log (6 : ℝ) := by rw [h₂]
  have hc : c = Real.log (7 : ℝ) / Real.log (6 : ℝ) := by
    apply (eq_div_iff_mul_eq hlog6ne0).mpr
    calc
      c * Real.log (6 : ℝ) = Real.log ((6 : ℝ) ^ c) := by rw [Real.log_rpow h6pos c]
      _ = Real.log (7 : ℝ) := by rw [h₃]
  have hd : d = Real.log (8 : ℝ) / Real.log (7 : ℝ) := by
    apply (eq_div_iff_mul_eq hlog7ne0).mpr
    calc
      d * Real.log (7 : ℝ) = Real.log ((7 : ℝ) ^ d) := by rw [Real.log_rpow h7pos d]
      _ = Real.log (8 : ℝ) := by rw [h₄]
  have hlog8 : Real.log (8 : ℝ) = (3 : ℝ) * Real.log (2 : ℝ) := by
    calc
      Real.log (8 : ℝ) = Real.log ((2 : ℝ) ^ (3 : ℕ)) := by norm_num
      _ = (3 : ℕ).cast * Real.log (2 : ℝ) := by rw [Real.log_pow]
      _ = (3 : ℝ) * Real.log (2 : ℝ) := by norm_num
  have hlog4 : Real.log (4 : ℝ) = (2 : ℝ) * Real.log (2 : ℝ) := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = (2 : ℕ).cast * Real.log (2 : ℝ) := by rw [Real.log_pow]
      _ = (2 : ℝ) * Real.log (2 : ℝ) := by norm_num
  calc
    a * b * c * d = ((Real.log (5 : ℝ) / Real.log (4 : ℝ)) * (Real.log (6 : ℝ) / Real.log (5 : ℝ)) *
      (Real.log (7 : ℝ) / Real.log (6 : ℝ)) * (Real.log (8 : ℝ) / Real.log (7 : ℝ))) := by
      simp [ha, hb, hc, hd]
    _ = Real.log (8 : ℝ) / Real.log (4 : ℝ) := by
      field_simp [hlog4ne0, hlog5ne0, hlog6ne0, hlog7ne0]
    _ = ((3 : ℝ) * Real.log (2 : ℝ)) / ((2 : ℝ) * Real.log (2 : ℝ)) := by rw [hlog8, hlog4]
    _ = (3 : ℝ) / (2 : ℝ) := by
      field_simp [hlog2ne0]
    _ = 3 / 2 := by norm_num
