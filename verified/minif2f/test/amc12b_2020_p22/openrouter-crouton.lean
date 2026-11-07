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
    calc
      (4 : ℝ) ^ t = ((2 : ℝ) ^ ((2 : ℕ) : ℝ)) ^ t := by
        rw [Real.rpow_natCast]; norm_num
      _ = (2 : ℝ) ^ (((2 : ℕ) : ℝ) * t) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ (t * ((2 : ℕ) : ℝ)) := by
        congr 1; push_cast; ring
      _ = ((2 : ℝ) ^ t) ^ ((2 : ℕ) : ℝ) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = ((2 : ℝ) ^ t) ^ 2 := by
        rw [Real.rpow_natCast]
  have hcont : Continuous fun t : ℝ => (2 : ℝ) ^ t - 6 * t := by
    have h2 : Continuous fun t : ℝ => (2 : ℝ) ^ t := by
      have heq : (fun t : ℝ => (2 : ℝ) ^ t)
          = fun t => Real.exp (Real.log 2 * t) := by
        funext t
        exact Real.rpow_def_of_pos (by norm_num) t
      rw [heq]
      exact Real.continuous_exp.comp (by fun_prop)
    exact h2.sub (by fun_prop)
  have hIVT := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
    hcont.continuousOn
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun t : ℝ => (2 : ℝ) ^ t - 6 * t) 1)
      ((fun t : ℝ => (2 : ℝ) ^ t - 6 * t) 0) := by
    constructor
    · show (2 : ℝ) ^ (1 : ℝ) - 6 * (1 : ℝ) ≤ 0
      rw [Real.rpow_one]; norm_num
    · show (0 : ℝ) ≤ (2 : ℝ) ^ (0 : ℝ) - 6 * (0 : ℝ)
      rw [Real.rpow_zero]; norm_num
  obtain ⟨t, htI, hteq⟩ := hIVT h0
  have hteq' : (2 : ℝ) ^ t - 6 * t = 0 := hteq
  have h2t : (2 : ℝ) ^ t = 6 * t := by linarith
  have ht_ne : t ≠ 0 := by
    intro ht0
    rw [ht0] at hteq'
    simp at hteq'
  refine ⟨?_, ?_⟩
  · refine ⟨t, ?_⟩
    rw [h4 t, h2t]
    field_simp [ht_ne]
    ring
  · intro y hy
    obtain ⟨t, rfl⟩ := hy
    have hpos : (0 : ℝ) < (4 : ℝ) ^ t :=
      Real.rpow_pos_of_pos (by norm_num) t
    rw [div_le_iff₀ hpos, h4 t]
    nlinarith [sq_nonneg ((2 : ℝ) ^ t - 6 * t)]
