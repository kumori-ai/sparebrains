import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sum1toneqn_prod1tonleq1 (a : ℕ → NNReal) (n : ℕ)
    (h₀ : ∑ x ∈ Finset.range n, a x = n) : ∏ x ∈ Finset.range n, a x ≤ 1 := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hnRpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hw_pos : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnRpos
    have hw : ∑ x ∈ Finset.range n, (fun _ : ℕ => (n : ℝ)⁻¹) x = 1 := by
      show ∑ x ∈ Finset.range n, (n : ℝ)⁻¹ = 1
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_inv_cancel₀ hnR
    have hw_nonneg : ∀ i ∈ Finset.range n, 0 ≤ (fun _ : ℕ => (n : ℝ)⁻¹) i :=
      fun i _ => le_of_lt hw_pos
    have hz_nonneg : ∀ i ∈ Finset.range n, 0 ≤ (fun x => (a x : ℝ)) i :=
      fun i _ => NNReal.coe_nonneg (a i)
    have hAM := Real.geom_mean_le_arith_mean_weighted (Finset.range n)
      (fun _ : ℕ => (n : ℝ)⁻¹) (fun x => (a x : ℝ)) hw_nonneg hw hz_nonneg
    have h0R : ∑ x ∈ Finset.range n, (a x : ℝ) = (n : ℝ) := by
      exact_mod_cast h₀
    have hRHS : ∑ x ∈ Finset.range n, (fun _ : ℕ => (n : ℝ)⁻¹) x * (a x : ℝ) = 1 := by
      show ∑ x ∈ Finset.range n, (n : ℝ)⁻¹ * (a x : ℝ) = 1
      rw [← Finset.mul_sum, h0R]
      exact inv_mul_cancel₀ hnR
    have hAM' : ∏ x ∈ Finset.range n, (a x : ℝ) ^ (n : ℝ)⁻¹ ≤ 1 := by
      rw [hRHS] at hAM
      exact hAM
    have hprod : ∏ x ∈ Finset.range n, (a x : ℝ) ^ (n : ℝ)⁻¹
        = (∏ x ∈ Finset.range n, (a x : ℝ)) ^ (n : ℝ)⁻¹ := by
      have hgen : ∀ s : Finset ℕ, ∏ x ∈ s, (a x : ℝ) ^ (n : ℝ)⁻¹
          = (∏ x ∈ s, (a x : ℝ)) ^ (n : ℝ)⁻¹ := by
        intro s
        induction s using Finset.induction with
        | empty => simp
        | insert x s hx ih =>
          rw [Finset.prod_insert hx, Finset.prod_insert hx,
            Real.mul_rpow (NNReal.coe_nonneg (a x))
              (Finset.prod_nonneg (fun i _ => NNReal.coe_nonneg (a i))), ih]
      exact hgen (Finset.range n)
    rw [hprod] at hAM'
    have hP : ∏ x ∈ Finset.range n, (a x : ℝ) ≤ 1 := by
      by_contra hlt
      have hlt : (1 : ℝ) < ∏ x ∈ Finset.range n, (a x : ℝ) := lt_of_not_ge hlt
      have hgt : (1 : ℝ) < (∏ x ∈ Finset.range n, (a x : ℝ)) ^ (n : ℝ)⁻¹ := by
        have h1 : (1 : ℝ) ^ (n : ℝ)⁻¹
            < (∏ x ∈ Finset.range n, (a x : ℝ)) ^ (n : ℝ)⁻¹ :=
          Real.rpow_lt_rpow (by norm_num) hlt hw_pos
        simpa using h1
      exact absurd hgt (not_lt_of_ge hAM')
    have hPnn : ((∏ x ∈ Finset.range n, a x : NNReal) : ℝ) ≤ 1 := by
      exact_mod_cast hP
    exact_mod_cast hPnn
