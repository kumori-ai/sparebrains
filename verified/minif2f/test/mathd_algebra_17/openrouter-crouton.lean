import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $$\sqrt{4+\sqrt{16+16a}}+ \sqrt{1+\sqrt{1+a}} = 6.$$ -/
theorem mathd_algebra_17 (a : ℝ)
    (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) :
    a = 8 := by
  have h_nonneg : 0 ≤ 1 + a := by
    by_contra h
    push_neg at h
    have h1 : Real.sqrt (1 + a) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt h)
    have h2 : Real.sqrt (16 + 16 * a) = 0 := by
      apply Real.sqrt_eq_zero_of_nonpos
      linarith
    rw [h1, h2] at h₀
    simp only [add_zero] at h₀
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [hs4, Real.sqrt_one] at h₀
    linarith
  set x := Real.sqrt (1 + a) with hx_def
  have hx_nonneg : 0 ≤ x := Real.sqrt_nonneg _
  have hx_sq : x ^ 2 = 1 + a := Real.sq_sqrt h_nonneg
  have h16 : Real.sqrt (16 + 16 * a) = 4 * x := by
    have heq : (16 + 16 * a) = (4 * x) ^ 2 := by
      calc (16 + 16 * a) = 16 * (1 + a) := by ring
        _ = 16 * x ^ 2 := by rw [← hx_sq]
        _ = (4 * x) ^ 2 := by ring
    rw [heq]
    exact Real.sqrt_sq (by linarith)
  rw [h16] at h₀
  have h1x_nonneg : 0 ≤ 1 + x := by linarith
  set y := Real.sqrt (1 + x) with hy_def
  have hy_nonneg : 0 ≤ y := Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = 1 + x := Real.sq_sqrt h1x_nonneg
  have h4 : Real.sqrt (4 + 4 * x) = 2 * y := by
    have heq : (4 + 4 * x) = (2 * y) ^ 2 := by
      calc (4 + 4 * x) = 4 * (1 + x) := by ring
        _ = 4 * y ^ 2 := by rw [← hy_sq]
        _ = (2 * y) ^ 2 := by ring
    rw [heq]
    exact Real.sqrt_sq (by linarith)
  rw [h4] at h₀
  have hy_eq : y = 2 := by linarith
  have h1x : 1 + x = 4 := by
    rw [hy_eq] at hy_sq
    linarith
  have hx_eq : x = 3 := by linarith
  have h1a : 1 + a = 9 := by
    rw [← hx_sq, hx_eq]
    norm_num
  linarith
