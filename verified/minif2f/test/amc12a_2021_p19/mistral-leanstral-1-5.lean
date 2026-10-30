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
  have hS : S = {0, π/2} := by
    ext x
    constructor
    · intro hx
      rcases (h₀ x).mp hx with ⟨hx0, hxπ, heq⟩
      have hπ2_pos : 0 < π/2 := by linarith [Real.pi_pos]
      have hcos_range : π/2 * Real.cos x ∈ Set.Icc (-(π/2)) (π/2) := by
        have hneg_one_le_cos : -1 ≤ Real.cos x := Real.neg_one_le_cos x
        have hcos_le_one : Real.cos x ≤ 1 := Real.cos_le_one x
        have h1 : -(π/2) ≤ π/2 * Real.cos x := by
          calc
            -(π/2) = (π/2) * (-1) := by ring
            _ ≤ (π/2) * Real.cos x := mul_le_mul_of_nonneg_left hneg_one_le_cos (by linarith)
        have h2 : π/2 * Real.cos x ≤ π/2 := by
          calc
            π/2 * Real.cos x ≤ (π/2) * 1 := mul_le_mul_of_nonneg_left hcos_le_one (by linarith)
            _ = π/2 := by ring
        exact ⟨h1, h2⟩
      have hsin_range : π/2 * (1 - Real.sin x) ∈ Set.Icc (-(π/2)) (π/2) := by
        have hsin_nonneg : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxπ
        have hsin_le_one : Real.sin x ≤ 1 := Real.sin_le_one x
        have h_nonneg : 0 ≤ 1 - Real.sin x := by linarith
        have h_le_one : 1 - Real.sin x ≤ 1 := by linarith
        have h1 : -(π/2) ≤ π/2 * (1 - Real.sin x) := by
          have : 0 ≤ π/2 * (1 - Real.sin x) := mul_nonneg (by linarith) h_nonneg
          linarith
        have h2 : π/2 * (1 - Real.sin x) ≤ π/2 := by
          calc
            π/2 * (1 - Real.sin x) ≤ (π/2) * 1 := mul_le_mul_of_nonneg_left h_le_one (by linarith)
            _ = π/2 := by ring
        exact ⟨h1, h2⟩
      have hinj : Set.InjOn Real.sin (Set.Icc (-(π/2)) (π/2)) :=
        Real.strictMonoOn_sin.injOn
      have heq' : Real.sin (π/2 * Real.cos x) = Real.sin (π/2 * (1 - Real.sin x)) := by
        calc
          Real.sin (π/2 * Real.cos x) = Real.cos (π/2 * Real.sin x) := heq
          _ = Real.sin (π/2 - (π/2 * Real.sin x)) := by rw [Real.sin_pi_div_two_sub]
          _ = Real.sin (π/2 * (1 - Real.sin x)) := by ring
      have h_eq_arg : π/2 * Real.cos x = π/2 * (1 - Real.sin x) :=
        hinj hcos_range hsin_range heq'
      have hπ2_ne_zero : π/2 ≠ 0 := by linarith
      have h_cos_eq : Real.cos x = 1 - Real.sin x :=
        mul_left_cancel₀ hπ2_ne_zero h_eq_arg
      have h_sum_eq_one : Real.sin x + Real.cos x = 1 := by linarith
      have h_sin_two_x_eq_zero : Real.sin (2*x) = 0 := by
        have h_sq_eq : (Real.sin x + Real.cos x)^2 = 1 := by rw [h_sum_eq_one, one_pow]
        have h_expand : (Real.sin x + Real.cos x)^2 = 1 + Real.sin (2*x) := by
          calc
            (Real.sin x + Real.cos x)^2 = Real.sin x ^ 2 + Real.cos x ^ 2 + 2 * Real.sin x * Real.cos x := by ring
            _ = (Real.sin x ^ 2 + Real.cos x ^ 2) + 2 * Real.sin x * Real.cos x := by ring
            _ = 1 + 2 * Real.sin x * Real.cos x := by rw [Real.sin_sq_add_cos_sq]
            _ = 1 + Real.sin (2*x) := by rw [← Real.sin_two_mul x]
        rw [h_expand] at h_sq_eq
        linarith
      rcases Real.sin_eq_zero_iff.mp h_sin_two_x_eq_zero with ⟨k, hk⟩
      have h2x_nonneg : 0 ≤ 2*x := by linarith
      have h2x_le_2pi : 2*x ≤ 2*π := by linarith
      have hk_nonneg : 0 ≤ (k : ℝ) := by
        have h_nonneg_mul : 0 ≤ (k : ℝ) * π := by
          linarith
        exact (mul_nonneg_iff_of_pos_right Real.pi_pos).mp h_nonneg_mul
      have hk_le_two : (k : ℝ) ≤ 2 := by
        have h_mul_le : (k : ℝ) * π ≤ 2 * π := by
          linarith
        exact (le_of_mul_le_mul_right h_mul_le Real.pi_pos)
      have hk_int_nonneg : (0 : ℤ) ≤ k := by exact_mod_cast hk_nonneg
      have hk_int_le_two : (k : ℤ) ≤ 2 := by exact_mod_cast hk_le_two
      have hk_cases : k = (0 : ℤ) ∨ k = (1 : ℤ) ∨ k = (2 : ℤ) := by
        omega
      rcases hk_cases with (hk0 | hk1 | hk2)
      · -- k = 0
        have hk0' : (k : ℝ) = 0 := by exact_mod_cast hk0
        have hx0' : x = 0 := by
          nlinarith
        simp [hx0']
      · -- k = 1
        have hk1' : (k : ℝ) = 1 := by exact_mod_cast hk1
        have hx_pi2 : x = π/2 := by
          nlinarith
        simp [hx_pi2]
      · -- k = 2
        have hk2' : (k : ℝ) = 2 := by exact_mod_cast hk2
        have hx_pi : x = π := by
          nlinarith
        have h_contra : Real.sin π + Real.cos π = 1 := by simpa [hx_pi] using h_sum_eq_one
        rw [Real.sin_pi, Real.cos_pi] at h_contra
        linarith
    · intro hx
      rcases Finset.mem_insert.mp hx with (hx | hx)
      · -- hx : x = 0
        subst x
        refine (h₀ 0).mpr ?_
        refine ⟨by norm_num, by linarith [Real.pi_pos], ?_⟩
        simp
      · -- hx : x ∈ {π/2}
        rcases Finset.mem_singleton.mp hx with rfl
        refine (h₀ (π/2)).mpr ?_
        refine ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos], ?_⟩
        simp
  rw [hS]
  have h0_ne_pi2 : (0 : ℝ) ≠ π/2 := by
    linarith [Real.pi_pos]
  simp [h0_ne_pi2]
