import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∑ k ∈ Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k < 198 := by
  -- inequality for each term: 1/√k < 2(√k - √(k-1))
  have hineq : ∀ k : ℕ, 2 ≤ k → 1 / Real.sqrt (k : ℝ) < 2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hk1pos : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    set a := Real.sqrt (k : ℝ) with ha
    set b := Real.sqrt ((k : ℝ) - 1) with hb
    have ha_pos : 0 < a := Real.sqrt_pos.mpr hkpos
    have hb_nonneg : 0 ≤ b := Real.sqrt_nonneg _
    have hb_lt_a : b < a := by
      refine Real.sqrt_lt_sqrt hk1pos ?_
      linarith
    have hsum_pos : 0 < a + b := by linarith
    have hsum_ne_zero : a + b ≠ 0 := by linarith
    have hprod : (a - b) * (a + b) = 1 := by
      calc
        (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
        _ = (Real.sqrt (k : ℝ)) ^ 2 - (Real.sqrt ((k : ℝ) - 1)) ^ 2 := by rfl
        _ = (k : ℝ) - ((k : ℝ) - 1) := by
          rw [Real.sq_sqrt (by linarith : 0 ≤ (k : ℝ)), Real.sq_sqrt hk1pos]
        _ = 1 := by ring
    have hsub_eq : a - b = 1 / (a + b) := by
      field_simp [hsum_ne_zero]
      exact hprod
    have h_main : 1 / a < 2 * (a - b) := by
      have hpos_a : 0 < a := ha_pos
      have hpos_ab : 0 < a + b := hsum_pos
      field_simp [hpos_a.ne.symm]
      rw [hsub_eq]
      field_simp [hpos_ab.ne.symm]
      nlinarith
    simpa [ha, hb] using h_main
  -- telescoping sum lemma
  have h_telescope_lemma : ∀ (a b : ℕ) (h : a ≤ b),
      ∑ k ∈ Finset.Icc a b, (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) =
      Real.sqrt (b : ℝ) - Real.sqrt ((a : ℝ) - 1) := by
    intro a b h
    have hbase : ∑ k ∈ Finset.Icc a a, (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) =
        Real.sqrt (a : ℝ) - Real.sqrt ((a : ℝ) - 1) := by
      have hIcc : Finset.Icc a a = {a} := by
        ext i; simp [Finset.mem_Icc, Finset.mem_singleton]
      rw [hIcc, Finset.sum_singleton]
    have hstep : ∀ b, a ≤ b → (∑ k ∈ Finset.Icc a b, (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) =
        Real.sqrt (b : ℝ) - Real.sqrt ((a : ℝ) - 1)) →
        (∑ k ∈ Finset.Icc a (b+1), (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) =
        Real.sqrt ((b+1 : ℕ) : ℝ) - Real.sqrt ((a : ℝ) - 1)) := by
      intro b hle hsum
      have hIcc_union : Finset.Icc a (b+1) = Finset.Icc a b ∪ {b+1} := by
        ext i; simp [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
      have hdisjoint : Disjoint (Finset.Icc a b) {b+1} := by
        refine Finset.disjoint_singleton_right.mpr ?_
        intro hmem
        rw [Finset.mem_Icc] at hmem
        omega
      rw [hIcc_union, Finset.sum_union hdisjoint, hsum, Finset.sum_singleton]
      push_cast
      ring
    exact Nat.le_induction hbase hstep b h
  have h_telescope : ∑ k ∈ Finset.Icc (2 : ℕ) 10000, (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) =
      Real.sqrt (10000 : ℝ) - Real.sqrt ((2 : ℝ) - 1) := by
    simpa using h_telescope_lemma 2 10000 (by omega)
  have h_sqrt10000 : Real.sqrt (10000 : ℝ) = 100 := by norm_num
  have h_sqrt2minus1 : Real.sqrt ((2 : ℝ) - 1) = 1 := by norm_num
  have h_sum_eq : ∑ k ∈ Finset.Icc (2 : ℕ) 10000, (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) = 99 := by
    rw [h_telescope, h_sqrt10000, h_sqrt2minus1]
    norm_num
  calc
    ∑ k ∈ Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k
        < ∑ k ∈ Finset.Icc (2 : ℕ) 10000, (2 * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1))) := by
      refine Finset.sum_lt_sum (fun i hi => ?_) ?_
      · have hi' : 2 ≤ i := (Finset.mem_Icc.mp hi).1
        exact le_of_lt (hineq i hi')
      · have h2mem : (2 : ℕ) ∈ Finset.Icc (2 : ℕ) 10000 := by
          refine Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        refine ⟨2, h2mem, ?_⟩
        exact hineq 2 (by omega)
    _ = 2 * ∑ k ∈ Finset.Icc (2 : ℕ) 10000, (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) := by
      rw [Finset.mul_sum]
    _ = 2 * 99 := by rw [h_sum_eq]
    _ = 198 := by norm_num
