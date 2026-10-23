import Mathlib

open scoped Nat
open scoped Real

/-- Given $2^a = 32$ and $a^b = 125$ find $b^a$. -/
theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  have h₂ : a = 5 := by
    have h₂₁ : Real.log ((2 : ℝ) ^ a) = Real.log 32 := by rw [h₀]
    have h₂₂ : Real.log ((2 : ℝ) ^ a) = a * Real.log 2 := by
      rw [Real.log_rpow] <;> norm_num
    have h₂₃ : Real.log 32 = Real.log (2 ^ 5) := by norm_num
    have h₂₄ : Real.log (2 ^ 5) = 5 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    have h₂₅ : a * Real.log 2 = 5 * Real.log 2 := by
      linarith
    have h₂₆ : Real.log 2 > 0 := by
      apply Real.log_pos
      norm_num
    have h₂₇ : a = 5 := by
      have h₂₈ : a * Real.log 2 = 5 * Real.log 2 := by linarith
      have h₂₉ : Real.log 2 ≠ 0 := by
        intro h
        linarith [h₂₆]
      apply mul_left_cancel₀ h₂₉
      linarith
    exact h₂₇
  have h₃ : b = 3 := by
    rw [h₂] at h₁
    have h₃₁ : (5 : ℝ) ^ b = 125 := by assumption
    have h₃₂ : Real.log ((5 : ℝ) ^ b) = Real.log 125 := by rw [h₃₁]
    have h₃₃ : Real.log ((5 : ℝ) ^ b) = b * Real.log 5 := by
      rw [Real.log_rpow] <;> norm_num
    have h₃₄ : Real.log 125 = Real.log (5 ^ 3) := by norm_num
    have h₃₅ : Real.log (5 ^ 3) = 3 * Real.log 5 := by
      rw [Real.log_pow] <;> norm_num
    have h₃₆ : b * Real.log 5 = 3 * Real.log 5 := by
      linarith
    have h₃₇ : Real.log 5 > 0 := by
      apply Real.log_pos
      norm_num
    have h₃₈ : b = 3 := by
      have h₃₉ : b * Real.log 5 = 3 * Real.log 5 := by linarith
      have h₄₀ : Real.log 5 ≠ 0 := by
        intro h
        linarith [h₃₇]
      apply mul_left_cancel₀ h₄₀
      linarith
    exact h₃₈
  rw [h₃, h₂]
  norm_num
