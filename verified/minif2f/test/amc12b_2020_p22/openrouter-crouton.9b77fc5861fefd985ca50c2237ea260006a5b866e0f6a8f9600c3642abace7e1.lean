import Mathlib

open scoped Nat
open scoped Real

/-- What is the maximum value of $\frac{(2^t-3t)t}{4^t}$ for real values of $t?$

$\textbf{(A)}\ \frac{1}{16} \qquad\textbf{(B)}\ \frac{1}{15} \qquad\textbf{(C)}\ \frac{1}{12} \qquad\textbf{(D)}\ \frac{1}{10} \qquad\textbf{(E)}\ \frac{1}{9}$ -/
theorem amc12b_2020_p22 :
    IsGreatest
      { ((2^t - 3 * t) * t) / (4^t) | (t : ℝ)}
      (1 / 12) := by
  have h4 : ∀ t : ℝ, (4 : ℝ) ^ t = ((2 : ℝ) ^ t) ^ 2 := by
    intro t
    rw [← Real.rpow_natCast ((2 : ℝ) ^ t) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h4eq : (4 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; norm_num
    rw [h4eq, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hexp : ∀ t : ℝ,
      ((2 ^ t - 3 * t) * t) / (4 ^ t) = t / (2 ^ t) - 3 * (t / (2 ^ t)) ^ 2 := by
    intro t
    rw [h4 t]
    have hne : (2 : ℝ) ^ t ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by norm_num) t)
    field_simp
  constructor
  · have hv4 : (2 : ℝ) ^ (4 : ℝ) = 16 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have hv6 : (2 : ℝ) ^ (6 : ℝ) = 64 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have hcont2 : Continuous fun t : ℝ => (2 : ℝ) ^ t := by
      have h : (fun t : ℝ => (2 : ℝ) ^ t) = fun t => Real.exp (Real.log 2 * t) := by
        funext t; rw [Real.rpow_def_of_pos (by norm_num)]
      rw [h]; fun_prop
    have hcont : Continuous fun t : ℝ => (2 : ℝ) ^ t - 6 * t :=
      hcont2.sub (by fun_prop)
    have hIVT := intermediate_value_Icc (show (4 : ℝ) ≤ 6 by norm_num) hcont.continuousOn
    have h0 : (0 : ℝ) ∈ Set.Icc ((2 : ℝ) ^ (4 : ℝ) - 6 * 4) ((2 : ℝ) ^ (6 : ℝ) - 6 * 6) := by
      rw [hv4, hv6]; constructor <;> norm_num
    obtain ⟨t0, ht0mem, ht0eq⟩ := hIVT h0
    have ht0eq' : (2 : ℝ) ^ t0 - 6 * t0 = 0 := ht0eq
    have ht0ge : (4 : ℝ) ≤ t0 := ht0mem.1
    have ht0pos : (0 : ℝ) < t0 := by linarith
    have ht0ne : t0 ≠ 0 := ne_of_gt ht0pos
    have h2t : (2 : ℝ) ^ t0 = 6 * t0 := sub_eq_zero.mp ht0eq'
    have hw : t0 / (2 : ℝ) ^ t0 = 1 / 6 := by
      rw [h2t, div_eq_iff (mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0) ht0ne)]
      ring
    refine ⟨t0, ?_⟩
    rw [hexp t0, hw]
    norm_num
  · intro y hy
    obtain ⟨t, rfl⟩ := hy
    rw [hexp t]
    have h : t / (2 ^ t) - 3 * (t / (2 ^ t)) ^ 2
        = 1 / 12 - (1 / 12) * (6 * (t / (2 ^ t)) - 1) ^ 2 := by ring
    rw [h]
    have hpos : (0 : ℝ) ≤ (1 / 12) * (6 * (t / (2 ^ t)) - 1) ^ 2 := by positivity
    linarith
