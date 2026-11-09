import Mathlib

open scoped Nat
open scoped Real

theorem induction_prod1p1onk3le3m1onn (n : ℕ) (h₀ : 0 < n) :
    ∏ k ∈ Finset.Icc 1 n, (1 + (1 : ℝ) / k ^ 3) ≤ (3 : ℝ) - 1 / ↑n := by
  have key : ∀ n : ℕ, 1 ≤ n →
      ∏ k ∈ Finset.Icc 1 n, (1 + (1 : ℝ) / k ^ 3) ≤ (3 : ℝ) - 1 / ↑n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        rw [Finset.Icc_self, Finset.prod_singleton]
        norm_num
    | succ m hm ih =>
        rw [Finset.prod_Icc_succ_top (by omega : (1 : ℕ) ≤ m + 1)]
        have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
        have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
        have hfactor : (0 : ℝ) ≤ 1 + 1 / ((m + 1 : ℕ) : ℝ) ^ 3 := by positivity
        have hle : (∏ k ∈ Finset.Icc 1 m, (1 + (1 : ℝ) / k ^ 3)) *
              (1 + 1 / ((m + 1 : ℕ) : ℝ) ^ 3)
            ≤ (3 - 1 / (m : ℝ)) * (1 + 1 / ((m + 1 : ℕ) : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right ih hfactor
        refine hle.trans ?_
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hdiff : (3 : ℝ) - 1 / ((m : ℝ) + 1) -
              (3 - 1 / (m : ℝ)) * (1 + 1 / ((m : ℝ) + 1) ^ 3)
            = ((m : ℝ) ^ 2 - (m : ℝ) + 2) / ((m : ℝ) * ((m : ℝ) + 1) ^ 3) := by
          field_simp [hm_pos.ne', hm1_pos.ne']
          ring
        have hnonneg : 0 ≤ ((m : ℝ) ^ 2 - (m : ℝ) + 2) /
            ((m : ℝ) * ((m : ℝ) + 1) ^ 3) := by
          apply div_nonneg
          · nlinarith [sq_nonneg ((m : ℝ) - 1), hm_pos]
          · exact mul_nonneg (le_of_lt hm_pos) (pow_nonneg (le_of_lt hm1_pos) 3)
        linarith
  exact key n h₀
