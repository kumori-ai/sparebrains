import Mathlib

open scoped Nat
open scoped Real

/--
How many solutions does the equation $\sin \left( \frac{\pi}2 \cos x\right)=\cos \left( \frac{\pi}2 \sin x\right)$ have in the closed interval $[0,\pi]$?


$\textbf{(A) }0 \qquad \textbf{(B) }1 \qquad \textbf{(C) }2 \qquad \textbf{(D) }3\qquad \textbf{(E) }4$ -/
theorem amc12a_2021_p19 (S : Finset ℝ)
    (h₀ :
      ∀ x : ℝ,
        x ∈ S ↔
          0 ≤ x ∧
            x ≤ Real.pi ∧
              Real.sin (Real.pi / 2 * Real.cos x) = Real.cos (Real.pi / 2 * Real.sin x)) :
    S.card = 2 := by
  have hS : S = {0, Real.pi / 2} := by
    ext x
    rw [h₀ x]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx0, hxpi, heq⟩
      have hpi : 0 < Real.pi := Real.pi_pos
      have hs : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
      have hs1 : Real.sin x ≤ 1 := Real.sin_le_one x
      have hc1 : -1 ≤ Real.cos x := Real.neg_one_le_cos x
      have hc2 : Real.cos x ≤ 1 := Real.cos_le_one x
      have hpi2pos : (0:ℝ) < Real.pi / 2 := by linarith
      have hpi2ne : Real.pi / 2 ≠ 0 := ne_of_gt hpi2pos
      have hU1 : -(Real.pi / 2) ≤ Real.pi / 2 * Real.cos x := by
        have h := mul_le_mul_of_nonneg_left hc1 (le_of_lt hpi2pos)
        linarith
      have hU2 : Real.pi / 2 * Real.cos x ≤ Real.pi / 2 := by
        have h := mul_le_mul_of_nonneg_left hc2 (le_of_lt hpi2pos)
        linarith
      have hV1 : 0 ≤ Real.pi / 2 - Real.pi / 2 * Real.sin x := by
        have h := mul_le_mul_of_nonneg_left hs1 (le_of_lt hpi2pos)
        linarith
      have hV2 : Real.pi / 2 - Real.pi / 2 * Real.sin x ≤ Real.pi / 2 := by
        have h := mul_nonneg (le_of_lt hpi2pos) hs
        linarith
      have hsin0 : Real.sin x = 0 → x = 0 ∨ x = Real.pi := by
        intro hs0
        by_contra hc
        push Not at hc
        have h1 : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hc.1)
        have h2 : x < Real.pi := lt_of_le_of_ne hxpi hc.2
        have hpos := Real.sin_pos_of_pos_of_lt_pi h1 h2
        linarith
      have hcos0 : Real.cos x = 0 → x = Real.pi / 2 := by
        intro hc0
        have hmem1 : x ∈ Set.Icc 0 Real.pi := ⟨hx0, hxpi⟩
        have hmem2 : Real.pi / 2 ∈ Set.Icc 0 Real.pi :=
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hinj := Real.strictAntiOn_cos.injOn hmem1 hmem2
        apply hinj
        rw [hc0, Real.cos_pi_div_two]
      have heq2 : Real.sin (Real.pi / 2 * Real.cos x)
          = Real.sin (Real.pi / 2 - Real.pi / 2 * Real.sin x) := by
        have hcos : Real.cos (Real.pi / 2 * Real.sin x)
            = Real.sin (Real.pi / 2 - Real.pi / 2 * Real.sin x) := by
          rw [Real.sin_pi_div_two_sub]
        rw [hcos] at heq
        exact heq
      obtain ⟨k, hk | hk⟩ := Real.sin_eq_sin_iff.mp heq2
      · -- Case V = U + 2kπ
        have hle : 2 * (k:ℝ) * Real.pi ≤ Real.pi := by linarith
        have hge : -(Real.pi / 2) ≤ 2 * (k:ℝ) * Real.pi := by linarith
        have h2k_le : (2:ℝ) * (k:ℝ) ≤ 1 := by nlinarith [Real.pi_pos, hle]
        have h2k_ge : (-1:ℝ) ≤ (2:ℝ) * (k:ℝ) := by nlinarith [Real.pi_pos, hge]
        have h2k_le_int : 2 * k ≤ 1 := by exact_mod_cast h2k_le
        have h2k_ge_int : -1 ≤ 2 * k := by exact_mod_cast h2k_ge
        have hk0 : k = 0 := by omega
        subst hk0
        simp at hk
        have hcos_eq : Real.cos x = 1 - Real.sin x := by
          have h : Real.pi / 2 * Real.cos x = Real.pi / 2 * (1 - Real.sin x) := by
            linarith
          exact mul_left_cancel₀ hpi2ne h
        have hsc : Real.sin x * Real.cos x = 0 := by
          have hsq : (Real.sin x + Real.cos x) ^ 2 = 1 := by
            have h : Real.sin x + Real.cos x = 1 := by linarith
            rw [h]; norm_num
          have hpyth := Real.sin_sq_add_cos_sq x
          nlinarith [hsq, hpyth]
        rcases mul_eq_zero.mp hsc with hs0 | hc0
        · rcases hsin0 hs0 with h | h
          · left; exact h
          · exfalso
            rw [h] at hcos_eq
            simp [Real.cos_pi, Real.sin_pi] at hcos_eq
            norm_num at hcos_eq
        · right; exact hcos0 hc0
      · -- Case V = π - U + 2kπ
        have hle : 2 * (k:ℝ) * Real.pi ≤ 0 := by linarith
        have hge : -(3 * Real.pi / 2) ≤ 2 * (k:ℝ) * Real.pi := by linarith
        have h2k_le : (2:ℝ) * (k:ℝ) ≤ 0 := by nlinarith [Real.pi_pos, hle]
        have h2k_ge : (-3 / 2 : ℝ) ≤ (2:ℝ) * (k:ℝ) := by nlinarith [Real.pi_pos, hge]
        have h2k_le_int : 2 * k ≤ 0 := by exact_mod_cast h2k_le
        have h2k_gt_int : -2 < 2 * k := by
          have h : (-2:ℝ) < (2:ℝ) * (k:ℝ) := by linarith
          exact_mod_cast h
        have hk0 : k = 0 := by omega
        subst hk0
        simp at hk
        have hcos_eq : Real.cos x = 1 + Real.sin x := by
          have h : Real.pi / 2 * Real.cos x = Real.pi / 2 * (1 + Real.sin x) := by
            linarith
          exact mul_left_cancel₀ hpi2ne h
        have hsc : Real.sin x * Real.cos x = 0 := by
          have hsq : (Real.cos x - Real.sin x) ^ 2 = 1 := by
            have h : Real.cos x - Real.sin x = 1 := by linarith
            rw [h]; norm_num
          have hpyth := Real.sin_sq_add_cos_sq x
          nlinarith [hsq, hpyth]
        rcases mul_eq_zero.mp hsc with hs0 | hc0
        · rcases hsin0 hs0 with h | h
          · left; exact h
          · exfalso
            rw [h] at hcos_eq
            simp [Real.cos_pi, Real.sin_pi] at hcos_eq
            norm_num at hcos_eq
        · right; exact hcos0 hc0
    · rintro (rfl | rfl)
      · refine ⟨le_refl 0, by linarith [Real.pi_pos], ?_⟩
        simp [Real.cos_zero, Real.sin_zero, Real.sin_pi_div_two]
      · refine ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos], ?_⟩
        simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  rw [hS, Finset.card_pair]
  have h : (0:ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  exact ne_of_lt h
