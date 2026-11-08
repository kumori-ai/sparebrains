import Mathlib

open scoped Nat
open scoped Real

theorem algebra_bleqa_apbon2msqrtableqambsqon8b (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : b ≤ a) :
    (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
  have ha := h₀.1
  have hb := h₀.2
  have hbpos : (0 : ℝ) < 8 * b := by linarith
  set x := Real.sqrt a with hx_def
  set y := Real.sqrt b with hy_def
  have hx2 : x ^ 2 = a := by
    have h := Real.sq_sqrt ha.le
    rwa [← hx_def] at h
  have hy2 : y ^ 2 = b := by
    have h := Real.sq_sqrt hb.le
    rwa [← hy_def] at h
  have hsqrt : Real.sqrt (a * b) = x * y := by
    have h := Real.sqrt_mul ha.le b
    rwa [← hx_def, ← hy_def] at h
  have hxy : y ≤ x := by
    have h := Real.sqrt_le_sqrt h₁
    rwa [← hx_def, ← hy_def] at h
  have hxpos : 0 < x := by
    rw [hx_def]
    exact Real.sqrt_pos.mpr ha
  have hypos : 0 < y := by
    rw [hy_def]
    exact Real.sqrt_pos.mpr hb
  have hprod : 0 ≤ (x - y) ^ 3 * (x + 3 * y) := by
    apply mul_nonneg
    · exact pow_nonneg (sub_nonneg.mpr hxy) 3
    · linarith
  rw [le_div_iff₀ hbpos, hsqrt, ← hx2, ← hy2]
  nlinarith [hprod]
