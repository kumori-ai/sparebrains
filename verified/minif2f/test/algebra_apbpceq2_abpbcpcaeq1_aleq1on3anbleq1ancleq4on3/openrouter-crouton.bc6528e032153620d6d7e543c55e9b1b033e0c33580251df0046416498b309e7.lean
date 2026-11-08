import Mathlib

open scoped Nat
open scoped Real

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  obtain ⟨hab_le, hbc_le⟩ := h₀
  have hs_ab : a + b = 2 - c := by linarith
  have hs_bc : b + c = 2 - a := by linarith
  have hs_ac : a + c = 2 - b := by linarith
  have hab_eq : a * b = (c - 1) ^ 2 := by
    have e : a * b = 1 - c * (a + b) := by
      have e1 : b * c + c * a = c * (a + b) := by ring
      linarith
    rw [e, hs_ab]; ring
  have hbc_eq : b * c = (a - 1) ^ 2 := by
    have e : b * c = 1 - a * (b + c) := by
      have e1 : c * a + a * b = a * (b + c) := by ring
      linarith
    rw [e, hs_bc]; ring
  have hca_eq : c * a = (b - 1) ^ 2 := by
    have e : c * a = 1 - b * (a + c) := by
      have e1 : a * b + b * c = b * (a + c) := by ring
      linarith
    rw [e, hs_ac]; ring
  have hab_nn : 0 ≤ a * b := by rw [hab_eq]; exact sq_nonneg _
  have hca_nn : 0 ≤ c * a := by rw [hca_eq]; exact sq_nonneg _
  have ha0 : 0 ≤ a := by
    by_contra h
    push_neg at h
    have hb0 : b ≤ 0 := by
      by_contra hb
      push_neg at hb
      have hneg : a * b < 0 := mul_neg_of_neg_of_pos h hb
      linarith
    have hc0 : c ≤ 0 := by
      by_contra hc
      push_neg at hc
      have hneg : c * a < 0 := mul_neg_of_pos_of_neg hc h
      linarith
    linarith
  have hb0 : 0 ≤ b := le_trans ha0 hab_le
  have hc0 : 0 ≤ c := le_trans hb0 hbc_le
  have hc_le : c ≤ 4 / 3 := by
    have hsq : 0 ≤ (a - b) ^ 2 := sq_nonneg _
    have e : (a - b) ^ 2 = c * (4 - 3 * c) := by
      have e1 : (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by ring
      rw [e1, hs_ab, hab_eq]; ring
    have hprod : 0 ≤ c * (4 - 3 * c) := by
      rw [← e]; exact hsq
    by_contra h
    push_neg at h
    have hcpos : 0 < c := by linarith
    have hneg : c * (4 - 3 * c) < 0 := mul_neg_of_pos_of_neg hcpos (by linarith)
    linarith
  have hb_le1 : b ≤ 1 := by
    by_contra h
    push_neg at h
    linarith
  have Pa_nn : 0 ≤ (3 * a - 1) * (a - 1) := by
    have e : (b - a) * (c - a) = (3 * a - 1) * (a - 1) := by
      have e1 : (b - a) * (c - a) = b * c - a * (b + c) + a ^ 2 := by ring
      rw [e1, hbc_eq, hs_bc]; ring
    have hnn : 0 ≤ (b - a) * (c - a) := mul_nonneg (by linarith) (by linarith)
    rw [← e]; exact hnn
  have Pb_nn : 0 ≤ -((3 * b - 1) * (b - 1)) := by
    have e : (b - a) * (c - b) = -((3 * b - 1) * (b - 1)) := by
      have e1 : (b - a) * (c - b) = b * (a + c) - c * a - b ^ 2 := by ring
      rw [e1, hs_ac, hca_eq]; ring
    have hnn : 0 ≤ (b - a) * (c - b) := mul_nonneg (by linarith) (by linarith)
    rw [← e]; exact hnn
  have Pc_nn : 0 ≤ (3 * c - 1) * (c - 1) := by
    have e : (c - a) * (c - b) = (3 * c - 1) * (c - 1) := by
      have e1 : (c - a) * (c - b) = c ^ 2 - c * (a + b) + a * b := by ring
      rw [e1, hs_ab, hab_eq]; ring
    have hnn : 0 ≤ (c - a) * (c - b) := mul_nonneg (by linarith) (by linarith)
    rw [← e]; exact hnn
  have ha_le : a ≤ 1 / 3 := by
    by_contra h
    push_neg at h
    have ha_lt1 : a < 1 := by linarith
    have hneg : (3 * a - 1) * (a - 1) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  have hb_ge : 1 / 3 ≤ b := by
    by_contra h
    push_neg at h
    have hpos : 0 < (3 * b - 1) * (b - 1) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
    linarith
  have hc_ge : 1 ≤ c := by
    by_contra h
    push_neg at h
    have hc_gt : 1 / 3 < c := by linarith
    have hneg : (3 * c - 1) * (c - 1) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  exact ⟨ha0, ha_le, hb_ge, hb_le1, hc_ge, hc_le⟩
