import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sum1toneqn_prod1tonleq1 (a : ℕ → NNReal) (n : ℕ)
    (h₀ : ∑ x ∈ Finset.range n, a x = n) : ∏ x ∈ Finset.range n, a x ≤ 1 := by
  by_cases hn : n = 0
  · aesop
  · have hn' : n ≠ 0 := hn
    have hsum : (∑ x ∈ Finset.range n, (a x : ℝ)) = (n : ℝ) := by exact_mod_cast h₀
    have hineq (x : NNReal) : (x : ℝ) ≤ Real.exp ((x : ℝ) - 1) := by
      have h := Real.add_one_le_exp ((x : ℝ) - 1)
      linarith
    have hprod_exp : (∏ x ∈ Finset.range n, (a x : ℝ)) ≤ (∏ x ∈ Finset.range n, Real.exp ((a x : ℝ) - 1)) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro i hi
        exact NNReal.coe_nonneg _
      · intro i hi
        exact hineq (a i)
    have hsum_one : (∑ x ∈ Finset.range n, (1 : ℝ)) = (n : ℝ) := by simp
    have hprod_eq : (∏ x ∈ Finset.range n, Real.exp ((a x : ℝ) - 1)) = (1 : ℝ) := by
      have hsum_sub : (∑ x ∈ Finset.range n, (↑(a x) - (1 : ℝ))) = (0 : ℝ) := by
        have hsum_a_real : ∑ x ∈ Finset.range n, (a x : ℝ) = (n : ℝ) := by
          have h := congrArg (fun s : NNReal => (s : ℝ)) h₀
          linarith
        calc
          ∑ x ∈ Finset.range n, ((a x : ℝ) - (1 : ℝ)) = (∑ x ∈ Finset.range n, (a x : ℝ)) - (∑ x ∈ Finset.range n, (1 : ℝ)) := by
            rw [Finset.sum_sub_distrib]
          _ = (n : ℝ) - (n : ℝ) := by rw [hsum_a_real, hsum_one]
          _ = 0 := by norm_num
      have hprod_eq : ∏ x ∈ Finset.range n, rexp (↑(a x) - (1 : ℝ)) = rexp (∑ x ∈ Finset.range n, (↑(a x) - (1 : ℝ))) := by
        exact Eq.symm (Real.exp_sum (Finset.range n) fun x => ↑(a x) - 1)
      have h_exp_zero : rexp (0 : ℝ) = (1 : ℝ) := by simp
      calc
        ∏ x ∈ Finset.range n, rexp (↑(a x) - (1 : ℝ)) = rexp (∑ x ∈ Finset.range n, (↑(a x) - (1 : ℝ))) := hprod_eq
        _ = rexp (0 : ℝ) := by rw [hsum_sub]
        _ = (1 : ℝ) := h_exp_zero
    have hprod_le_one : (∏ x ∈ Finset.range n, (a x : ℝ)) ≤ (1 : ℝ) := by
      linarith
    exact_mod_cast hprod_le_one