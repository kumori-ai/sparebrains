import Mathlib

open scoped Nat
open scoped Real

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  rcases h₀ with ⟨ha_le_b, hb_le_c⟩
  have ha_le_c : a ≤ c := le_trans ha_le_b hb_le_c
  have hb_ge_a : 0 ≤ b - a := sub_nonneg.mpr ha_le_b
  have hc_ge_a : 0 ≤ c - a := sub_nonneg.mpr ha_le_c
  have hc_ge_b : 0 ≤ c - b := sub_nonneg.mpr hb_le_c
  have hb_le_c' : b - c ≤ 0 := sub_nonpos.mpr hb_le_c
  have ha_nonneg : 0 ≤ a := by
    have h_sq_ineq : (b + c)^2 ≥ 4 * (b * c) := by
      have h : (b - c)^2 ≥ 0 := sq_nonneg _
      nlinarith
    have h_sum : b + c = 2 - a := by nlinarith
    have h_prod : b * c = 1 - 2*a + a^2 := by nlinarith
    rw [h_sum, h_prod] at h_sq_ineq
    nlinarith
  have ha_le_third : a ≤ 1/3 := by
    have h_nonneg : (b - a) * (c - a) ≥ 0 := mul_nonneg hb_ge_a hc_ge_a
    have h_expand : (b - a) * (c - a) = 3*a^2 - 4*a + 1 := by nlinarith
    rw [h_expand] at h_nonneg
    have h_factor : 3*a^2 - 4*a + 1 = (3*a - 1) * (a - 1) := by ring
    rw [h_factor] at h_nonneg
    have ha_lt_one : a < 1 := by
      by_contra! hge
      have hb_ge_one : 1 ≤ b := le_trans hge ha_le_b
      have hc_ge_one : 1 ≤ c := le_trans hb_ge_one hb_le_c
      nlinarith
    have h_neg : a - 1 < 0 := by linarith
    have h_nonpos : 3*a - 1 ≤ 0 := by
      nlinarith
    nlinarith
  have hb_bounds : 1/3 ≤ b ∧ b ≤ 1 := by
    have h_nonpos : (b - a) * (b - c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb_ge_a hb_le_c'
    have h_expand : (b - a) * (b - c) = 3*b^2 - 4*b + 1 := by nlinarith
    rw [h_expand] at h_nonpos
    have h_factor : 3*b^2 - 4*b + 1 = (3*b - 1) * (b - 1) := by ring
    rw [h_factor] at h_nonpos
    have hb_le_one : b ≤ 1 := by
      by_contra! hgt
      have hpos : 0 < b - 1 := by linarith
      have hpos3 : 0 < 3*b - 1 := by nlinarith
      nlinarith
    have hb_ge_third : 1/3 ≤ b := by
      by_contra! hlt
      have hneg3 : 3*b - 1 < 0 := by nlinarith
      have hneg1 : b - 1 < 0 := by nlinarith
      nlinarith
    exact And.intro hb_ge_third hb_le_one
  rcases hb_bounds with ⟨hb_ge_third, hb_le_one⟩
  have hc_ge_one : 1 ≤ c := by
    have h_nonneg : (c - a) * (c - b) ≥ 0 := mul_nonneg hc_ge_a hc_ge_b
    have h_expand : (c - a) * (c - b) = 3*c^2 - 4*c + 1 := by nlinarith
    rw [h_expand] at h_nonneg
    have h_factor : 3*c^2 - 4*c + 1 = (3*c - 1) * (c - 1) := by ring
    rw [h_factor] at h_nonneg
    have hc_gt_third : 1/3 < c := by
      by_contra! hle
      have hb_le_third : b ≤ 1/3 := le_trans hb_le_c hle
      have ha_le_third' : a ≤ 1/3 := le_trans ha_le_b hb_le_third
      nlinarith
    have hpos3 : 0 < 3*c - 1 := by nlinarith
    have h_nonneg_c_minus_one : 0 ≤ c - 1 := by
      nlinarith
    nlinarith
  have hc_le_four_thirds : c ≤ 4/3 := by
    have h_sq_ineq : (a + b)^2 ≥ 4 * (a * b) := by
      have h : (a - b)^2 ≥ 0 := sq_nonneg _
      nlinarith
    have h_sum : a + b = 2 - c := by nlinarith
    have h_prod : a * b = 1 - 2*c + c^2 := by nlinarith
    rw [h_sum, h_prod] at h_sq_ineq
    nlinarith
  exact ⟨ha_nonneg, ha_le_third, hb_ge_third, hb_le_one, hc_ge_one, hc_le_four_thirds⟩
