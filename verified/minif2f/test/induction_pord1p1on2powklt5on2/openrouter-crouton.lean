import Mathlib

open scoped Nat
open scoped Real

theorem induction_pord1p1on2powklt5on2 (n : ℕ) (h₀ : 0 < n) :
    ∏ k ∈ Finset.Icc 1 n, (1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := by
  have aux : ∀ n : ℕ, 2 ≤ n →
      ∏ k ∈ Finset.Icc 1 n, (1 + (1 : ℝ) / 2 ^ k) ≤ 5 / 2 * (1 - 1 / 2 ^ n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have h : Finset.Icc 1 2 = {1, 2} := by decide
      rw [h, Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2)]
      norm_num
    | succ n hn ih =>
      show ∏ k ∈ Finset.Icc 1 (n + 1), (1 + (1 : ℝ) / 2 ^ k) ≤
        5 / 2 * (1 - 1 / 2 ^ (n + 1))
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hpos : (0 : ℝ) ≤ 1 + (1 : ℝ) / 2 ^ (n + 1) := by positivity
      have hle := mul_le_mul_of_nonneg_right ih hpos
      have hsucc : (1 : ℝ) / 2 ^ (n + 1) = (1 / 2 ^ n) / 2 := by
        rw [pow_succ, div_div]
      refine le_trans hle ?_
      rw [hsucc]
      nlinarith [sq_nonneg ((1 : ℝ) / 2 ^ n)]
  by_cases hn2 : 2 ≤ n
  · have h := aux n hn2
    have hx : (0 : ℝ) < (1 : ℝ) / 2 ^ n := by positivity
    have hlt : 5 / 2 * (1 - (1 : ℝ) / 2 ^ n) < 5 / 2 := by linarith
    linarith
  · have hn1 : n = 1 := by omega
    subst hn1
    have h : Finset.Icc 1 1 = {1} := by decide
    rw [h, Finset.prod_singleton]
    norm_num
