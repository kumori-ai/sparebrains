import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $$\sqrt{4+\sqrt{16+16a}}+ \sqrt{1+\sqrt{1+a}} = 6.$$ -/
theorem mathd_algebra_17 (a : ℝ)
    (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) :
    a = 8 := by
  -- First, show that 1 + a ≥ 0, otherwise the equation cannot hold.
  have h1a_nonneg : 0 ≤ 1 + a := by
    by_contra! h_neg
    -- h_neg : 1 + a < 0
    have h_sqrt1a_zero : Real.sqrt (1 + a) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (by linarith)
    have h_sqrt16a_zero : Real.sqrt (16 + 16 * a) = 0 := by
      have h_nonpos : 16 + 16 * a ≤ 0 := by nlinarith
      exact Real.sqrt_eq_zero_of_nonpos h_nonpos
    have h_lhs : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 3 := by
      rw [h_sqrt16a_zero, h_sqrt1a_zero]
      norm_num
    rw [h_lhs] at h₀
    norm_num at h₀
  set x := Real.sqrt (1 + a) with hx_def
  have hx_nonneg : 0 ≤ x := Real.sqrt_nonneg _
  have hx_sq : x ^ 2 = 1 + a := Real.sq_sqrt h1a_nonneg
  have h16 : (0 : ℝ) ≤ 16 := by norm_num
  have h_sqrt16 : Real.sqrt (16 + 16 * a) = 4 * x := by
    calc
      Real.sqrt (16 + 16 * a) = Real.sqrt (16 * (1 + a)) := by ring
      _ = Real.sqrt (16 : ℝ) * Real.sqrt (1 + a) := by rw [Real.sqrt_mul h16]
      _ = 4 * x := by norm_num [hx_def]
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have h1x_nonneg : 0 ≤ 1 + x := by linarith
  have h_sqrt_first : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 2 * Real.sqrt (1 + x) := by
    calc
      Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = Real.sqrt (4 + 4 * x) := by rw [h_sqrt16]
      _ = Real.sqrt (4 * (1 + x)) := by ring
      _ = Real.sqrt (4 : ℝ) * Real.sqrt (1 + x) := by rw [Real.sqrt_mul h4]
      _ = 2 * Real.sqrt (1 + x) := by norm_num
  have h_second : Real.sqrt (1 + Real.sqrt (1 + a)) = Real.sqrt (1 + x) := by
    rw [hx_def]
  have h_eq : 3 * Real.sqrt (1 + x) = 6 := by
    linarith
  have h_sqrt_eq : Real.sqrt (1 + x) = 2 := by
    linarith
  have h_1x_eq_4 : 1 + x = 4 := by
    have h_sq : (Real.sqrt (1 + x)) ^ 2 = 2 ^ 2 := by rw [h_sqrt_eq]
    have h_sq' : (Real.sqrt (1 + x)) ^ 2 = 1 + x := Real.sq_sqrt h1x_nonneg
    linarith
  have hx_eq_3 : x = 3 := by
    linarith
  have h_sqrt1a_eq_3 : Real.sqrt (1 + a) = 3 := by
    rw [← hx_def, hx_eq_3]
  have h_1a_eq_9 : 1 + a = 9 := by
    have h_sq : (Real.sqrt (1 + a)) ^ 2 = 3 ^ 2 := by rw [h_sqrt1a_eq_3]
    have h_sq' : (Real.sqrt (1 + a)) ^ 2 = 1 + a := Real.sq_sqrt h1a_nonneg
    linarith
  linarith
