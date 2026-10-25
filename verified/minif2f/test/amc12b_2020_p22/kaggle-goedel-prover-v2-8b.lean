import Mathlib

open scoped Nat
open scoped Real

/-- What is the maximum value of $\frac{(2^t-3t)t}{4^t}$ for real values of $t?$

$\textbf{(A)}\ \frac{1}{16} \qquad\textbf{(B)}\ \frac{1}{15} \qquad\textbf{(C)}\ \frac{1}{12} \qquad\textbf{(D)}\ \frac{1}{10} \qquad\textbf{(E)}\ \frac{1}{9}$ -/
theorem amc12b_2020_p22 :
    IsGreatest
      { ((2^t - 3 * t) * t) / (4^t) | (t : ℝ)}
      (1 / 12) := by
  have h₁ : (1 / 12 : ℝ) ∈ { ((2^t - 3 * t) * t) / (4^t) | (t : ℝ)} := by
    have h₂ : ∃ (t : ℝ), ((2 : ℝ) ^ t - 3 * t) * t / (4 : ℝ) ^ t = 1 / 12 := by
      -- Use the Intermediate Value Theorem to find a t such that 6 * t = 2 ^ t
      have h₃ : (4 : ℝ) < 5 := by norm_num
      have h₄ : ContinuousOn (fun t : ℝ => (6 : ℝ) * t - (2 : ℝ) ^ t) (Set.Icc 4 5) := by
        apply ContinuousOn.sub
        · exact ContinuousOn.mul continuousOn_const continuousOn_id
        · exact ContinuousOn.rpow (continuousOn_const) (continuousOn_id) (fun x hx => by norm_num [hx.1, hx.2])
      have h₅ : ∃ t ∈ Set.Icc 4 5, (6 : ℝ) * t - (2 : ℝ) ^ t = 0 := by
        have h₅₁ : (4 : ℝ) ∈ Set.Icc 4 5 := by norm_num
        have h₅₂ : (5 : ℝ) ∈ Set.Icc 4 5 := by norm_num
        have h₅₃ : (6 : ℝ) * (4 : ℝ) - (2 : ℝ) ^ (4 : ℝ) > 0 := by norm_num
        have h₅₄ : (6 : ℝ) * (5 : ℝ) - (2 : ℝ) ^ (5 : ℝ) < 0 := by norm_num
        have h₅₅ : ContinuousOn (fun t : ℝ => (6 : ℝ) * t - (2 : ℝ) ^ t) (Set.Icc 4 5) := h₄
        have h₅₆ : ∃ t ∈ Set.Icc 4 5, (6 : ℝ) * t - (2 : ℝ) ^ t = 0 := by
          apply intermediate_value_Icc' (by norm_num) h₅₅
          constructor <;> norm_num at h₅₃ h₅₄ ⊢ <;> linarith
        exact h₅₆
      obtain ⟨t, ⟨ht₁, ht₂⟩, ht₃⟩ := h₅
      use t
      have h₆ : (6 : ℝ) * t = (2 : ℝ) ^ t := by linarith
      have h₇ : ((2 : ℝ) ^ t - 3 * t) * t / (4 : ℝ) ^ t = 1 / 12 := by
        have h₇₁ : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ ( (2 : ℝ) ) by norm_num]
          rw [← Real.rpow_mul] <;> ring_nf <;> norm_num
          <;> linarith
        rw [h₇₁]
        have h₇₂ : (2 : ℝ) ^ (2 * t) = (2 : ℝ) ^ t * (2 : ℝ) ^ t := by
          rw [show (2 * t : ℝ) = t + t by ring]
          rw [Real.rpow_add (by norm_num : (2 : ℝ) > 0)]
          <;> ring_nf
        rw [h₇₂]
        have h₇₃ : (2 : ℝ) ^ t = 6 * t := by linarith
        rw [h₇₃]
        have h₇₄ : t > 0 := by linarith
        field_simp [h₇₄.ne']
        <;> ring_nf at *
        <;> nlinarith
      exact h₇
    obtain ⟨t, ht⟩ := h₂
    exact ⟨t, by simpa using ht⟩
  
  have h₂ : ∀ (x : ℝ), x ∈ { ((2^t - 3 * t) * t) / (4^t) | (t : ℝ)} → x ≤ (1 / 12 : ℝ) := by
    intro x hx
    rcases hx with ⟨t, rfl⟩
    have h₃ : ((2 : ℝ) ^ t - 3 * t) * t / (4 : ℝ) ^ t ≤ 1 / 12 := by
      have h₄ : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ ( (2 : ℝ) ) by norm_num]
        rw [← Real.rpow_mul] <;> ring_nf <;> norm_num
        <;> linarith
      rw [h₄]
      have h₅ : (2 : ℝ) ^ (2 * t) = (2 : ℝ) ^ t * (2 : ℝ) ^ t := by
        rw [show (2 * t : ℝ) = t + t by ring]
        rw [Real.rpow_add (by norm_num : (2 : ℝ) > 0)]
        <;> ring_nf
      rw [h₅]
      have h₆ : ((2 : ℝ) ^ t - 3 * t) * t / ((2 : ℝ) ^ t * (2 : ℝ) ^ t) = (t / (2 : ℝ) ^ t) - 3 * (t / (2 : ℝ) ^ t) ^ 2 := by
        have h₇ : (2 : ℝ) ^ t > 0 := Real.rpow_pos_of_pos (by norm_num) t
        field_simp [h₇.ne']
        <;> ring_nf
        <;> field_simp [h₇.ne']
        <;> ring_nf
        <;> nlinarith
      rw [h₆]
      have h₇ : (t / (2 : ℝ) ^ t : ℝ) - 3 * (t / (2 : ℝ) ^ t : ℝ) ^ 2 ≤ 1 / 12 := by
        have h₈ : (t / (2 : ℝ) ^ t : ℝ) - 3 * (t / (2 : ℝ) ^ t : ℝ) ^ 2 ≤ 1 / 12 := by
          have h₉ : ∀ (y : ℝ), y - 3 * y ^ 2 ≤ 1 / 12 := by
            intro y
            nlinarith [sq_nonneg (y - 1 / 6)]
          exact h₉ (t / (2 : ℝ) ^ t)
        exact h₈
      exact h₇
    exact h₃
  
  have h_main : IsGreatest { ((2^t - 3 * t) * t) / (4^t) | (t : ℝ)} (1 / 12) := by
    refine' ⟨h₁, _⟩
    intro x hx
    have h₃ : x ≤ (1 / 12 : ℝ) := h₂ x hx
    exact h₃
  
  exact h_main
