import Mathlib

open scoped Nat
open scoped Real

theorem algebra_bleqa_apbon2msqrtableqambsqon8b (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : b ≤ a) :
    (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
  have hbpos : 0 < b := h₀.2
  have hapos : 0 < a := h₀.1
  have hb_nonneg : 0 ≤ b := le_of_lt hbpos
  have hratio_nonneg : 0 ≤ a / b := div_nonneg (le_of_lt hapos) hb_nonneg
  have hratio_ge_one : 1 ≤ a / b := by
    rw [le_div_iff₀ hbpos]
    simpa using h₁
  let x : ℝ := Real.sqrt (a / b)
  have hx_nonneg : 0 ≤ x := Real.sqrt_nonneg _
  have hx_ge_one : 1 ≤ x := by
    dsimp [x]
    exact (Real.one_le_sqrt).2 hratio_ge_one
  have hx_sq : x ^ 2 = a / b := by
    dsimp [x]
    exact Real.sq_sqrt hratio_nonneg
  have ha_eq : a = b * x ^ 2 := by
    rw [hx_sq]
    field_simp [hbpos.ne']
  have hsqrt_ab : Real.sqrt (a * b) = b * x := by
    have hprod : a * b = (b * x) ^ 2 := by
      rw [ha_eq]
      ring
    rw [hprod]
    exact Real.sqrt_sq (mul_nonneg hb_nonneg hx_nonneg)
  have hineq : 4 * (x - 1) ^ 2 ≤ (x ^ 2 - 1) ^ 2 := by
    have hx1 : 0 ≤ x - 1 := by linarith
    have hx3 : 0 ≤ x + 3 := by linarith
    have hfac : (x ^ 2 - 1) ^ 2 - 4 * (x - 1) ^ 2 = (x - 1) ^ 3 * (x + 3) := by
      ring
    have hnonneg : 0 ≤ (x - 1) ^ 3 * (x + 3) := by
      exact mul_nonneg (pow_nonneg hx1 3) hx3
    nlinarith [hfac, hnonneg]
  have hmain : b * (x - 1) ^ 2 / 2 ≤ b * (x ^ 2 - 1) ^ 2 / 8 := by
    have hb8 : 0 ≤ b / 8 := div_nonneg hb_nonneg (by norm_num : (0 : ℝ) ≤ 8)
    have hmul := mul_le_mul_of_nonneg_left hineq hb8
    nlinarith [hmul]
  calc
    (a + b) / 2 - Real.sqrt (a * b) = b * (x - 1) ^ 2 / 2 := by
      rw [hsqrt_ab, ha_eq]
      ring
    _ ≤ b * (x ^ 2 - 1) ^ 2 / 8 := hmain
    _ = (a - b) ^ 2 / (8 * b) := by
      rw [ha_eq]
      field_simp [hbpos.ne']
