import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∑ k ∈ Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k < 198 := by
  have hterm : ∀ k : ℕ, 2 ≤ k →
      1 / Real.sqrt (k : ℝ) <
        2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) := by
    intro k hk
    have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    have ha_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hb_lt : Real.sqrt ((k - 1 : ℕ) : ℝ) < Real.sqrt (k : ℝ) := by
      apply Real.sqrt_lt_sqrt
      · positivity
      · rw [hcast]; linarith
    have hprod : (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) *
        (Real.sqrt (k : ℝ) + Real.sqrt ((k - 1 : ℕ) : ℝ)) = 1 := by
      have h1 : (Real.sqrt (k : ℝ)) ^ 2 = (k : ℝ) := Real.sq_sqrt (by linarith)
      have h2 : (Real.sqrt ((k - 1 : ℕ) : ℝ)) ^ 2 = ((k - 1 : ℕ) : ℝ) :=
        Real.sq_sqrt (by positivity)
      have h3 : (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) *
          (Real.sqrt (k : ℝ) + Real.sqrt ((k - 1 : ℕ) : ℝ)) =
          (Real.sqrt (k : ℝ)) ^ 2 - (Real.sqrt ((k - 1 : ℕ) : ℝ)) ^ 2 := by ring
      rw [h3, h1, h2, hcast]
      ring
    have hsum_pos : 0 < Real.sqrt (k : ℝ) + Real.sqrt ((k - 1 : ℕ) : ℝ) := by
      have hnn : 0 ≤ Real.sqrt ((k - 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
      linarith
    have hdiff : Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ) =
        1 / (Real.sqrt (k : ℝ) + Real.sqrt ((k - 1 : ℕ) : ℝ)) := by
      rw [eq_div_iff (ne_of_gt hsum_pos)]
      exact hprod
    have hgt : 1 / (2 * Real.sqrt (k : ℝ)) <
        1 / (Real.sqrt (k : ℝ) + Real.sqrt ((k - 1 : ℕ) : ℝ)) := by
      apply one_div_lt_one_div_of_lt hsum_pos
      linarith [hb_lt]
    have heq : 1 / Real.sqrt (k : ℝ) = 2 * (1 / (2 * Real.sqrt (k : ℝ))) := by
      field_simp
    calc 1 / Real.sqrt (k : ℝ) = 2 * (1 / (2 * Real.sqrt (k : ℝ))) := heq
      _ < 2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) := by
          rw [hdiff]; linarith [hgt]
  have key : ∀ N : ℕ, 2 ≤ N →
      ∑ k ∈ Finset.Icc 2 N, 1 / Real.sqrt (k : ℝ) <
        2 * (Real.sqrt (N : ℝ) - 1) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
        simp only [Finset.Icc_self, Finset.sum_singleton]
        have h := hterm 2 (le_refl 2)
        have h1 : Real.sqrt ((2 - 1 : ℕ) : ℝ) = 1 := by norm_num
        rw [h1] at h
        exact h
    | succ n hn ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
        have h := hterm (n + 1) (by omega)
        simp only [Nat.add_sub_cancel] at h
        linarith [ih, h]
  have h10000 := key 10000 (by norm_num)
  have hsqrt : Real.sqrt ((10000 : ℕ) : ℝ) = 100 := by
    rw [show ((10000 : ℕ) : ℝ) = (100 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsqrt] at h10000
  linarith [h10000]
