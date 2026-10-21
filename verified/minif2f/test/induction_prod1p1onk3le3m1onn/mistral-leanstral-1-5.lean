import Mathlib

open scoped Nat
open scoped Real

theorem induction_prod1p1onk3le3m1onn (n : ℕ) (h₀ : 0 < n) :
    ∏ k ∈ Finset.Icc 1 n, (1 + (1 : ℝ) / k ^ 3) ≤ (3 : ℝ) - 1 / ↑n := by
  have hn1 : 1 ≤ n := by omega
  refine Nat.le_induction ?base ?step n hn1
  · -- base case n = 1
    simp [Finset.Icc_self, Finset.prod_singleton]
    norm_num
  · -- step: assume for m, 1 ≤ m, prove for m+1
    intro m hm h_ih
    rw [Finset.prod_Icc_succ_top (by omega : (1 : ℕ) ≤ m.succ)]
    have h_nonneg : 0 ≤ 1 + (1 : ℝ) / (m.succ : ℝ) ^ 3 := by positivity
    have h_ineq : (3 - 1 / (m : ℝ)) * (1 + (1 : ℝ) / (m.succ : ℝ) ^ 3) ≤ 3 - 1 / (m.succ : ℝ) := by
      have ha_pos : 0 < (m : ℝ) := by exact_mod_cast (Nat.one_pos.trans_le hm)
      have hb_pos : 0 < (m.succ : ℝ) := by exact_mod_cast Nat.succ_pos m
      have ha_ne_zero : (m : ℝ) ≠ 0 := by linarith
      have hb_ne_zero : (m.succ : ℝ) ≠ 0 := by linarith
      have ha_ge_one : 1 ≤ (m : ℝ) := by exact_mod_cast hm
      have hb_eq : (m.succ : ℝ) = (m : ℝ) + 1 := by simp
      field_simp [ha_ne_zero, hb_ne_zero]
      nlinarith [hb_eq, ha_ge_one]
    exact (mul_le_mul_of_nonneg_right h_ih h_nonneg).trans h_ineq
