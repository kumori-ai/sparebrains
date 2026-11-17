import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have ha_le_one : a ≤ 1 := by
    nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  have ha_ge_neg_one : -1 ≤ a := by
    nlinarith [sq_nonneg b, sq_nonneg (a + 1)]
  have hb_le_one : b ≤ 1 := by
    nlinarith [sq_nonneg a, sq_nonneg (b - 1)]
  have hb_ge_neg_one : -1 ≤ b := by
    nlinarith [sq_nonneg a, sq_nonneg (b + 1)]
  have h₁ : a - b ≤ 1 - a * b := by
    have hb_nonneg : 0 ≤ 1 + b := by linarith
    have hnonneg : 0 ≤ (1 - a) * (1 + b) :=
      mul_nonneg (sub_nonneg.mpr ha_le_one) hb_nonneg
    nlinarith
  have h₂ : -(1 - a * b) ≤ a - b := by
    have ha_nonneg : 0 ≤ 1 + a := by linarith
    have hnonneg : 0 ≤ (1 - b) * (1 + a) :=
      mul_nonneg (sub_nonneg.mpr hb_le_one) ha_nonneg
    nlinarith
  have habs : |a - b| ≤ 1 - a * b := abs_le.mpr ⟨h₂, h₁⟩
  rw [Real.norm_eq_abs]
  linarith
