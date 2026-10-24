import Mathlib

open scoped Nat
open scoped Real

/--
Suppose that  $4^{a}=5$, $5^{b}=6$, $6^{c}=7,$ and  $7^{d}=8$. What is $a\cdot b\cdot c\cdot d$? -/
theorem mathd_algebra_598 (a b c d : ℝ) (h₁ : (4 : ℝ) ^ a = 5) (h₂ : (5 : ℝ) ^ b = 6)
    (h₃ : (6 : ℝ) ^ c = 7) (h₄ : (7 : ℝ) ^ d = 8) : a * b * c * d = 3 / 2 := by
  have h₁' : a = Real.log 5 / Real.log 4 := by
    have h₁a : Real.log ((4 : ℝ) ^ a) = Real.log 5 := by rw [h₁]
    have h₁b : a * Real.log 4 = Real.log 5 := by
      rw [Real.log_rpow (by norm_num)] at h₁a
      exact h₁a
    have h₁c : Real.log 4 ≠ 0 := by
      have : Real.log 4 > 0 := Real.log_pos (by norm_num)
      linarith
    field_simp at h₁b ⊢
    nlinarith
  have h₂' : b = Real.log 6 / Real.log 5 := by
    have h₂a : Real.log ((5 : ℝ) ^ b) = Real.log 6 := by rw [h₂]
    have h₂b : b * Real.log 5 = Real.log 6 := by
      rw [Real.log_rpow (by norm_num)] at h₂a
      exact h₂a
    have h₂c : Real.log 5 ≠ 0 := by
      have : Real.log 5 > 0 := Real.log_pos (by norm_num)
      linarith
    field_simp at h₂b ⊢
    nlinarith
  have h₃' : c = Real.log 7 / Real.log 6 := by
    have h₃a : Real.log ((6 : ℝ) ^ c) = Real.log 7 := by rw [h₃]
    have h₃b : c * Real.log 6 = Real.log 7 := by
      rw [Real.log_rpow (by norm_num)] at h₃a
      exact h₃a
    have h₃c : Real.log 6 ≠ 0 := by
      have : Real.log 6 > 0 := Real.log_pos (by norm_num)
      linarith
    field_simp at h₃b ⊢
    nlinarith
  have h₄' : d = Real.log 8 / Real.log 7 := by
    have h₄a : Real.log ((7 : ℝ) ^ d) = Real.log 8 := by rw [h₄]
    have h₄b : d * Real.log 7 = Real.log 8 := by
      rw [Real.log_rpow (by norm_num)] at h₄a
      exact h₄a
    have h₄c : Real.log 7 ≠ 0 := by
      have : Real.log 7 > 0 := Real.log_pos (by norm_num)
      linarith
    field_simp at h₄b ⊢
    nlinarith
  rw [h₁', h₂', h₃', h₄']
  have h₅ : Real.log 4 ≠ 0 := by
    have : Real.log 4 > 0 := Real.log_pos (by norm_num)
    linarith
  have h₆ : Real.log 5 ≠ 0 := by
    have : Real.log 5 > 0 := Real.log_pos (by norm_num)
    linarith
  have h₇ : Real.log 6 ≠ 0 := by
    have : Real.log 6 > 0 := Real.log_pos (by norm_num)
    linarith
  have h₈ : Real.log 7 ≠ 0 := by
    have : Real.log 7 > 0 := Real.log_pos (by norm_num)
    linarith
  field_simp [h₅, h₆, h₇, h₈]
  have h₉ : Real.log 8 = 3 * Real.log 2 := by
    have : Real.log 8 = Real.log (2 ^ 3) := by norm_num
    rw [this]
    rw [Real.log_pow]
    <;> norm_num
  have h₁₀ : Real.log 4 = 2 * Real.log 2 := by
    have : Real.log 4 = Real.log (2 ^ 2) := by norm_num
    rw [this]
    rw [Real.log_pow]
    <;> norm_num
  rw [h₉, h₁₀]
  have h₁₁ : Real.log 2 ≠ 0 := by
    have : Real.log 2 > 0 := Real.log_pos (by norm_num)
    linarith
  field_simp [h₁₁]
  <;> ring
  <;> norm_num
