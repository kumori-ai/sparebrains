import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $$\sqrt{4+\sqrt{16+16a}}+ \sqrt{1+\sqrt{1+a}} = 6.$$ -/
theorem mathd_algebra_17 (a : ℝ)
    (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) :
    a = 8 := by
  have h_sqrt16 : Real.sqrt (16 + 16 * a) = 4 * Real.sqrt (1 + a) := by
    have h_eq : (16 + 16 * a : ℝ) = 16 * (1 + a) := by ring
    rw [h_eq, Real.sqrt_mul (show (0 : ℝ) ≤ 16 by norm_num) (1 + a)]
    have h16 : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (show (0 : ℝ) ≤ 4 by norm_num)]
    rw [h16]
  have h_first : Real.sqrt (4 + Real.sqrt (16 + 16 * a))
      = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
    rw [h_sqrt16]
    have h_eq : (4 + 4 * Real.sqrt (1 + a) : ℝ) = 4 * (1 + Real.sqrt (1 + a)) := by ring
    rw [h_eq, Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num) (1 + Real.sqrt (1 + a))]
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [h4]
  rw [h_first] at h₀
  have hv : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by linarith
  have hv_sq : (Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2 = 1 + Real.sqrt (1 + a) :=
    Real.sq_sqrt (by have h := Real.sqrt_nonneg (1 + a); linarith)
  rw [hv] at hv_sq
  have hu : Real.sqrt (1 + a) = 3 := by
    norm_num at hv_sq
    linarith
  have h_nonneg : 0 ≤ 1 + a := by
    by_contra hlt
    have hlt' : 1 + a < 0 := lt_of_not_ge hlt
    have h1 : Real.sqrt (1 + a) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt hlt')
    linarith
  have hu_sq : (Real.sqrt (1 + a)) ^ 2 = 1 + a := Real.sq_sqrt h_nonneg
  rw [hu] at hu_sq
  norm_num at hu_sq
  linarith
