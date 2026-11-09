import Mathlib

open scoped Nat
open scoped Real

/--
Given that $\sum_{k=1}^{35}\sin 5k=\tan \frac mn,$ where angles are measured in degrees, and $m$ and $n$ are relatively prime positive integers that satisfy $\frac mn< 90,$ find $m+n.$ -/
theorem aime_1999_p11 (m : ℚ) (h₀ : 0 < m)
    (h₁ : ∑ k ∈ Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * π / 180) = Real.tan (m * π / 180))
    (h₂ : (m.num : ℝ) / m.den < 90) : ↑m.den + m.num = 177 := by
  set x : ℝ := Real.pi / 36 with hx
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hx_pos : 0 < x := by
    rw [hx]
    positivity
  have hsin_ne : Real.sin (x / 2) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hident : ∀ A B : ℝ, Real.cos (A - B) - Real.cos (A + B) = 2 * Real.sin A * Real.sin B := by
    intro A B
    rw [Real.cos_sub, Real.cos_add]
    ring
  have hsum : ∀ N : ℕ, 2 * Real.sin (x / 2) * (∑ k ∈ Finset.Icc 1 N, Real.sin (k * x))
      = Real.cos (x / 2) - Real.cos (((N : ℝ) + 1 / 2) * x) := by
    intro N
    induction N with
    | zero =>
      have hempty : Finset.Icc (1 : ℕ) 0 = ∅ := Finset.Icc_eq_empty (by norm_num)
      rw [hempty, Finset.sum_empty, mul_zero]
      push_cast
      have e : ((0 : ℝ) + 1 / 2) * x = x / 2 := by ring
      rw [e]
      simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1)]
      push_cast at ih ⊢
      have h3 := hident (((N : ℝ) + 1) * x) (x / 2)
      have e1 : ((N : ℝ) + 1 + 1 / 2) * x = ((N : ℝ) + 1) * x + x / 2 := by ring
      have e2 : ((N : ℝ) + 1) * x - x / 2 = ((N : ℝ) + 1 / 2) * x := by ring
      grind
  have h35 := hsum 35
  push_cast at h35
  have hcos35 : Real.cos (((35 : ℝ) + 1 / 2) * x) = -Real.cos (x / 2) := by
    have e : ((35 : ℝ) + 1 / 2) * x = Real.pi - x / 2 := by
      rw [hx]; ring
    rw [e, Real.cos_pi_sub]
  rw [hcos35] at h35
  have hS : (∑ k ∈ Finset.Icc (1 : ℕ) 35, Real.sin (k * x)) = Real.cos (x / 2) / Real.sin (x / 2) := by
    rw [eq_div_iff hsin_ne]
    linear_combination h35 / 2
  have hsum_eq : (∑ k ∈ Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * π / 180))
      = ∑ k ∈ Finset.Icc (1 : ℕ) 35, Real.sin (k * x) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    rw [hx]; ring
  have htan_val : Real.tan (35 * Real.pi / 72) = Real.cos (x / 2) / Real.sin (x / 2) := by
    have e : 35 * Real.pi / 72 = Real.pi / 2 - x / 2 := by
      rw [hx]; ring
    rw [e, Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  have htan_eq : Real.tan ((m : ℝ) * Real.pi / 180) = Real.tan (35 * Real.pi / 72) := by
    calc Real.tan ((m : ℝ) * Real.pi / 180)
        = ∑ k ∈ Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * π / 180) := h₁.symm
      _ = ∑ k ∈ Finset.Icc (1 : ℕ) 35, Real.sin (k * x) := hsum_eq
      _ = Real.cos (x / 2) / Real.sin (x / 2) := hS
      _ = Real.tan (35 * Real.pi / 72) := htan_val.symm
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast h₀
  have hm90 : (m : ℝ) < 90 := by
    have hcast : (m : ℝ) = (m.num : ℝ) / (m.den : ℝ) := by
      have h := Rat.num_div_den m
      have h2 : (((m.num : ℚ) / (m.den : ℚ) : ℚ) : ℝ) = (m : ℝ) := by rw [h]
      push_cast at h2
      exact h2.symm
    rw [hcast]
    exact h₂
  have hmem_m : (m : ℝ) * Real.pi / 180 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have hpos : 0 < (m : ℝ) * Real.pi / 180 := by
        apply div_pos (mul_pos hm_pos hpi_pos) (by norm_num)
      linarith
    · have h1 : (m : ℝ) * Real.pi < 90 * Real.pi := mul_lt_mul_of_pos_right hm90 hpi_pos
      linarith
  have hmem_35 : 35 * Real.pi / 72 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have harg : (m : ℝ) * Real.pi / 180 = 35 * Real.pi / 72 :=
    Real.strictMonoOn_tan.injOn hmem_m hmem_35 htan_eq
  have hmul : (m : ℝ) * Real.pi = (175 / 2) * Real.pi := by
    have h180 : ((m : ℝ) * Real.pi / 180) * 180 = (35 * Real.pi / 72) * 180 := by rw [harg]
    linear_combination h180
  have hm_real : (m : ℝ) = 175 / 2 := mul_right_cancel₀ Real.pi_ne_zero hmul
  have hm_val : m = 175 / 2 := by
    have h : (m : ℝ) = ((175 / 2 : ℚ) : ℝ) := by
      push_cast
      exact hm_real
    exact_mod_cast h
  rw [hm_val]
  have hnum : (175 / 2 : ℚ).num = 175 := by
    norm_num
  have hden : (175 / 2 : ℚ).den = 2 := by
    norm_num
  rw [hnum, hden]
  norm_num
