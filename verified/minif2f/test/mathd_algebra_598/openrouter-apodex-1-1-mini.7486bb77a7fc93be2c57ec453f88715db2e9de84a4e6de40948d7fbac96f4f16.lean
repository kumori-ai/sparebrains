import Mathlib

open scoped Nat
open scoped Real

/--
Suppose that  $4^{a}=5$, $5^{b}=6$, $6^{c}=7,$ and  $7^{d}=8$. What is $a\cdot b\cdot c\cdot d$? -/
theorem mathd_algebra_598 (a b c d : ℝ) (h₁ : (4 : ℝ) ^ a = 5) (h₂ : (5 : ℝ) ^ b = 6)
    (h₃ : (6 : ℝ) ^ c = 7) (h₄ : (7 : ℝ) ^ d = 8) : a * b * c * d = 3 / 2 := by
  have h₅ : a = Real.log 5 / Real.log 4 := by
    have h : Real.log ((4 : ℝ) ^ a) = Real.log 5 := by rw [h₁]
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 4)] at h
    rw [mul_comm] at h
    have h₆ : Real.log 4 ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num
    field_simp [h₆] at h ⊢
    linarith
  have h₇ : b = Real.log 6 / Real.log 5 := by
    have h : Real.log ((5 : ℝ) ^ b) = Real.log 6 := by rw [h₂]
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 5)] at h
    rw [mul_comm] at h
    have h₈ : Real.log 5 ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num
    field_simp [h₈] at h ⊢
    linarith
  have h₉ : c = Real.log 7 / Real.log 6 := by
    have h : Real.log ((6 : ℝ) ^ c) = Real.log 7 := by rw [h₃]
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 6)] at h
    rw [mul_comm] at h
    have h₁₀ : Real.log 6 ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num
    field_simp [h₁₀] at h ⊢
    linarith
  have h₁₁ : d = Real.log 8 / Real.log 7 := by
    have h : Real.log ((7 : ℝ) ^ d) = Real.log 8 := by rw [h₄]
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 7)] at h
    rw [mul_comm] at h
    have h₁₂ : Real.log 7 ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num
    field_simp [h₁₂] at h ⊢
    linarith
  calc
    a * b * c * d = (Real.log 5 / Real.log 4) * (Real.log 6 / Real.log 5) * (Real.log 7 / Real.log 6) * (Real.log 8 / Real.log 7) := by
      rw [h₅, h₇, h₉, h₁₁]
    _ = Real.log 8 / Real.log 4 := by
      field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≠ 1),
                  Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 5) (by norm_num : (5 : ℝ) ≠ 1),
                  Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 6) (by norm_num : (6 : ℝ) ≠ 1),
                  Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 7) (by norm_num : (7 : ℝ) ≠ 1)]
      <;> ring
      <;> norm_num
    _ = 3 / 2 := by
      have h₁₃ : Real.log 8 = (3 / 2 : ℝ) * Real.log 4 := by
        have h₁₄ : (8 : ℝ) = (4 : ℝ) ^ (3 / 2 : ℝ) := by norm_num
        rw [h₁₄]
        rw [Real.log_rpow (by norm_num : (0 : ℝ) < 4)]
      rw [h₁₃]
      field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≠ 1)]
