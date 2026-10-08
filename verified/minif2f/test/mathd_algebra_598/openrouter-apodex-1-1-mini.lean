import Mathlib

open scoped Nat
open scoped Real

/--
Suppose that  $4^{a}=5$, $5^{b}=6$, $6^{c}=7,$ and  $7^{d}=8$. What is $a\cdot b\cdot c\cdot d$? -/
theorem mathd_algebra_598 (a b c d : ℝ) (h₁ : (4 : ℝ) ^ a = 5) (h₂ : (5 : ℝ) ^ b = 6)
    (h₃ : (6 : ℝ) ^ c = 7) (h₄ : (7 : ℝ) ^ d = 8) : a * b * c * d = 3 / 2 := by
  have h₅ : a = Real.log 5 / Real.log 4 := by
    have h : Real.log ((4 : ℝ) ^ a) = Real.log 5 := by rw [h₁]
    rw [Real.log_rpow (by norm_num : (4 : ℝ) > 0)] at h
    field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (4 : ℝ) > 0) (by norm_num : (4 : ℝ) ≠ 1)] at h ⊢
    exact h
  have h₆ : b = Real.log 6 / Real.log 5 := by
    have h : Real.log ((5 : ℝ) ^ b) = Real.log 6 := by rw [h₂]
    rw [Real.log_rpow (by norm_num : (5 : ℝ) > 0)] at h
    field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (5 : ℝ) > 0) (by norm_num : (5 : ℝ) ≠ 1)] at h ⊢
    exact h
  have h₇ : c = Real.log 7 / Real.log 6 := by
    have h : Real.log ((6 : ℝ) ^ c) = Real.log 7 := by rw [h₃]
    rw [Real.log_rpow (by norm_num : (6 : ℝ) > 0)] at h
    field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (6 : ℝ) > 0) (by norm_num : (6 : ℝ) ≠ 1)] at h ⊢
    exact h
  have h₈ : d = Real.log 8 / Real.log 7 := by
    have h : Real.log ((7 : ℝ) ^ d) = Real.log 8 := by rw [h₄]
    rw [Real.log_rpow (by norm_num : (7 : ℝ) > 0)] at h
    field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (7 : ℝ) > 0) (by norm_num : (7 : ℝ) ≠ 1)] at h ⊢
    exact h
  rw [h₅, h₆, h₇, h₈]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (4 : ℝ) > 0) (by norm_num : (4 : ℝ) ≠ 1),
              Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (5 : ℝ) > 0) (by norm_num : (5 : ℝ) ≠ 1),
              Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (6 : ℝ) > 0) (by norm_num : (6 : ℝ) ≠ 1),
              Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (7 : ℝ) > 0) (by norm_num : (7 : ℝ) ≠ 1)]
  have h₉ : Real.log 8 = (3 / 2 : ℝ) * Real.log 4 := by
    have h₁₀ : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num]
      simp
    have h₁₁ : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
      simp
    rw [h₁₀, h₁₁]
    ring
  rw [h₉]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (4 : ℝ) > 0) (by norm_num : (4 : ℝ) ≠ 1)]
