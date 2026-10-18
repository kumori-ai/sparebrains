import Mathlib

open scoped Nat
open scoped Real

theorem algebra_bleqa_apbon2msqrtableqambsqon8b (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : b ≤ a) :
    (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
  rcases h₀ with ⟨ha, hb⟩
  have ha' : 0 ≤ a := ha.le
  have hb' : 0 ≤ b := hb.le
  set s := Real.sqrt a with hs_def
  set t := Real.sqrt b with ht_def
  have hs_sq : s ^ 2 = a := Real.sq_sqrt ha'
  have ht_sq : t ^ 2 = b := Real.sq_sqrt hb'
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
  have hst : t ≤ s := Real.sqrt_le_sqrt h₁
  have hpos_t : 0 < t := Real.sqrt_pos.mpr hb
  have hpos_t_sq : 0 < t ^ 2 := pow_pos hpos_t 2
  have hLHS' : (a + b) / 2 - Real.sqrt (a * b) = (s - t) ^ 2 / 2 := by
    calc
      (a + b) / 2 - Real.sqrt (a * b) = (s ^ 2 + t ^ 2) / 2 - (s * t) := by
        rw [hs_sq, ht_sq, Real.sqrt_mul ha' b, hs_def, ht_def]
      _ = (s - t) ^ 2 / 2 := by ring
  have hRHS : (a - b) ^ 2 / (8 * b) = (s - t) ^ 2 * (s + t) ^ 2 / (8 * t ^ 2) := by
    calc
      (a - b) ^ 2 / (8 * b) = ((s ^ 2 - t ^ 2) ^ 2) / (8 * (t ^ 2)) := by
        rw [hs_sq, ht_sq]
      _ = ((s - t) * (s + t) * (s - t) * (s + t)) / (8 * t ^ 2) := by ring
      _ = (s - t) ^ 2 * (s + t) ^ 2 / (8 * t ^ 2) := by ring
  have h_ineq : 4 * t ^ 2 ≤ (s + t) ^ 2 := by
    nlinarith [hst, hs_nonneg, ht_nonneg]
  have h_sq_nonneg : 0 ≤ (s - t) ^ 2 := pow_two_nonneg _
  have h_mul : 8 * t ^ 2 * (s - t) ^ 2 ≤ 2 * (s + t) ^ 2 * (s - t) ^ 2 := by
    have h_nonneg : 0 ≤ 2 * (s - t) ^ 2 := by nlinarith
    calc
      8 * t ^ 2 * (s - t) ^ 2 = (4 * t ^ 2) * (2 * (s - t) ^ 2) := by ring
      _ ≤ (s + t) ^ 2 * (2 * (s - t) ^ 2) := mul_le_mul_of_nonneg_right h_ineq h_nonneg
      _ = 2 * (s + t) ^ 2 * (s - t) ^ 2 := by ring
  have h_main : (s - t) ^ 2 / 2 ≤ (s - t) ^ 2 * (s + t) ^ 2 / (8 * t ^ 2) := by
    field_simp [hpos_t_sq.ne.symm, show (2 : ℝ) ≠ 0 from by norm_num]
    linarith
  calc
    (a + b) / 2 - Real.sqrt (a * b) = (s - t) ^ 2 / 2 := hLHS'
    _ ≤ (s - t) ^ 2 * (s + t) ^ 2 / (8 * t ^ 2) := h_main
    _ = (a - b) ^ 2 / (8 * b) := by rw [hRHS]
