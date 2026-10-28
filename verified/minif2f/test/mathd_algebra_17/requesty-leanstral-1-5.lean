import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $$\sqrt{4+\sqrt{16+16a}}+ \sqrt{1+\sqrt{1+a}} = 6.$$ -/
theorem mathd_algebra_17 (a : ℝ)
    (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) :
    a = 8 := by
  have h_sqrt_eq : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
    calc
      Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = Real.sqrt (4 + Real.sqrt (16 * (1 + a))) := by ring
      _ = Real.sqrt (4 + Real.sqrt (16 : ℝ) * Real.sqrt (1 + a)) := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16) (1 + a)]
      _ = Real.sqrt (4 + 4 * Real.sqrt (1 + a)) := by norm_num
      _ = Real.sqrt (4 * (1 + Real.sqrt (1 + a))) := by ring
      _ = Real.sqrt (4 : ℝ) * Real.sqrt (1 + Real.sqrt (1 + a)) := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) _]
      _ = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by norm_num
  rw [h_sqrt_eq] at h₀
  have h_sum : 3 * Real.sqrt (1 + Real.sqrt (1 + a)) = 6 := by linarith
  have h_sqrt_eq2 : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by linarith
  have h_nonneg_inner : 0 ≤ 1 + Real.sqrt (1 + a) := by
    have : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg _
    linarith
  have h_sq_eq : (Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2 = 4 := by
    rw [h_sqrt_eq2]
    norm_num
  have h_eq_inner : 1 + Real.sqrt (1 + a) = 4 := by
    rw [Real.sq_sqrt h_nonneg_inner] at h_sq_eq
    exact h_sq_eq
  have h_sqrt_eq3 : Real.sqrt (1 + a) = 3 := by linarith
  have h_nonneg_a : 0 ≤ 1 + a := by
    by_contra! hneg
    have hsqrt0 : Real.sqrt (1 + a) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    rw [hsqrt0] at h_sqrt_eq3
    linarith
  have h_sq_eq2 : (Real.sqrt (1 + a)) ^ 2 = 9 := by
    rw [h_sqrt_eq3]
    norm_num
  have h_eq_a : 1 + a = 9 := by
    rw [Real.sq_sqrt h_nonneg_a] at h_sq_eq2
    exact h_sq_eq2
  linarith
