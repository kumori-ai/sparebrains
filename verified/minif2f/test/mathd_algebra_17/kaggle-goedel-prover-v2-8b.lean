import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $$\sqrt{4+\sqrt{16+16a}}+ \sqrt{1+\sqrt{1+a}} = 6.$$ -/
theorem mathd_algebra_17 (a : ℝ)
    (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) :
    a = 8 := by
  have h₁ : a ≥ -1 := by
    by_contra h
    have h₂ : a < -1 := by linarith
    have h₃ : Real.sqrt (16 + 16 * a) = 0 := by
      have h₄ : 16 + 16 * a < 0 := by
        nlinarith
      rw [Real.sqrt_eq_zero_of_nonpos] <;> nlinarith
    have h₄ : Real.sqrt (1 + a) = 0 := by
      have h₅ : 1 + a < 0 := by nlinarith
      rw [Real.sqrt_eq_zero_of_nonpos] <;> nlinarith
    have h₅ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 2 := by
      rw [h₃]
      rw [Real.sqrt_eq_iff_eq_sq] <;> nlinarith [Real.sqrt_nonneg 4, Real.sq_sqrt (show 0 ≤ 4 by norm_num)]
    have h₆ : Real.sqrt (1 + Real.sqrt (1 + a)) = 1 := by
      rw [h₄]
      rw [Real.sqrt_eq_iff_eq_sq] <;> nlinarith [Real.sqrt_nonneg 1, Real.sq_sqrt (show 0 ≤ 1 by norm_num)]
    rw [h₅, h₆] at h₀
    norm_num at h₀
    <;> linarith
  
  have h₂ : Real.sqrt (16 + 16 * a) = 4 * Real.sqrt (1 + a) := by
    have h₂₁ : 0 ≤ 1 + a := by linarith
    have h₂₂ : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg (1 + a)
    have h₂₃ : 0 ≤ 16 + 16 * a := by nlinarith
    have h₂₄ : Real.sqrt (16 + 16 * a) = 4 * Real.sqrt (1 + a) := by
      have h₂₄₁ : Real.sqrt (16 + 16 * a) = Real.sqrt (16 * (1 + a)) := by ring_nf
      rw [h₂₄₁]
      have h₂₄₂ : Real.sqrt (16 * (1 + a)) = 4 * Real.sqrt (1 + a) := by
        rw [Real.sqrt_eq_iff_eq_sq (by nlinarith) (by nlinarith [Real.sqrt_nonneg (1 + a), Real.sq_sqrt (by linarith : 0 ≤ (1 + a : ℝ))])]
        nlinarith [Real.sqrt_nonneg (1 + a), Real.sq_sqrt (by linarith : 0 ≤ (1 + a : ℝ))]
      rw [h₂₄₂]
    exact h₂₄
  
  have h₃ : Real.sqrt (4 + 4 * Real.sqrt (1 + a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by
    have h₃₁ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = Real.sqrt (4 + 4 * Real.sqrt (1 + a)) := by
      rw [h₂]
      <;> ring_nf
    rw [h₃₁] at h₀
    exact h₀
  
  have h₄ : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by
    have h₄₁ : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg (1 + a)
    have h₄₂ : 0 ≤ 1 + Real.sqrt (1 + a) := by nlinarith
    have h₄₃ : 0 ≤ Real.sqrt (4 + 4 * Real.sqrt (1 + a)) := Real.sqrt_nonneg _
    have h₄₄ : Real.sqrt (4 + 4 * Real.sqrt (1 + a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
      have h₄₄₁ : Real.sqrt (4 + 4 * Real.sqrt (1 + a)) = Real.sqrt (4 * (1 + Real.sqrt (1 + a))) := by ring_nf
      rw [h₄₄₁]
      have h₄₄₂ : Real.sqrt (4 * (1 + Real.sqrt (1 + a))) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
        rw [Real.sqrt_eq_iff_eq_sq (by nlinarith) (by nlinarith [Real.sqrt_nonneg (1 + Real.sqrt (1 + a)), Real.sq_sqrt (by nlinarith : 0 ≤ (1 + Real.sqrt (1 + a) : ℝ))])]
        nlinarith [Real.sqrt_nonneg (1 + Real.sqrt (1 + a)), Real.sq_sqrt (by nlinarith : 0 ≤ (1 + Real.sqrt (1 + a) : ℝ))]
      rw [h₄₄₂]
    rw [h₄₄] at h₃
    have h₄₅ : 2 * Real.sqrt (1 + Real.sqrt (1 + a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by linarith
    have h₄₆ : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by
      nlinarith
    exact h₄₆
  
  have h₅ : Real.sqrt (1 + a) = 3 := by
    have h₅₁ : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := h₄
    have h₅₂ : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg (1 + a)
    have h₅₃ : 0 ≤ 1 + Real.sqrt (1 + a) := by nlinarith
    have h₅₄ : (Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2 = 1 + Real.sqrt (1 + a) := by
      rw [Real.sq_sqrt] <;> nlinarith
    rw [h₅₁] at h₅₄
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + a by linarith)]
  
  have h₆ : a = 8 := by
    have h₆₁ : Real.sqrt (1 + a) = 3 := h₅
    have h₆₂ : 0 ≤ 1 + a := by
      by_contra h₆₂
      have h₆₃ : 1 + a < 0 := by linarith
      have h₆₄ : Real.sqrt (1 + a) = 0 := by
        rw [Real.sqrt_eq_zero_of_nonpos] <;> linarith
      rw [h₆₄] at h₆₁
      norm_num at h₆₁
    have h₆₃ : (Real.sqrt (1 + a)) ^ 2 = 1 + a := by
      rw [Real.sq_sqrt] <;> linarith
    rw [h₆₁] at h₆₃
    nlinarith
  
  exact h₆
