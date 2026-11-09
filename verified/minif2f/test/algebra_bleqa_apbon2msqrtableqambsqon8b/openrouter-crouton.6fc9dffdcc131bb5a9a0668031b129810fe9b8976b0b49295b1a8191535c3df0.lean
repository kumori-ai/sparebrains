import Mathlib

open scoped Nat
open scoped Real

theorem algebra_bleqa_apbon2msqrtableqambsqon8b (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : b ≤ a) :
    (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
  have ha_pos : 0 < a := h₀.1
  have hb_pos : 0 < b := h₀.2
  set x := Real.sqrt a with hx_def
  set y := Real.sqrt b with hy_def
  have hx2 : x ^ 2 = a := by
    rw [hx_def]
    exact Real.sq_sqrt (le_of_lt ha_pos)
  have hy2 : y ^ 2 = b := by
    rw [hy_def]
    exact Real.sq_sqrt (le_of_lt hb_pos)
  have hx_pos : 0 < x := by
    rw [hx_def]
    exact Real.sqrt_pos.mpr ha_pos
  have hy_pos : 0 < y := by
    rw [hy_def]
    exact Real.sqrt_pos.mpr hb_pos
  have hxy : y ≤ x := by
    rw [hx_def, hy_def]
    exact Real.sqrt_le_sqrt h₁
  have hprod : Real.sqrt (a * b) = x * y := by
    rw [hx_def, hy_def, Real.sqrt_mul (le_of_lt ha_pos)]
  rw [hprod, ← hx2, ← hy2]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * y ^ 2)]
  nlinarith [mul_nonneg (pow_nonneg (sub_nonneg.mpr hxy) 3)
    (show (0 : ℝ) ≤ x + 3 * y by linarith)]
