import Mathlib

open scoped Nat
open scoped Real

/--
If $\left(\sqrt[4]{11}\right)^{3x-3}=\frac{1}{5}$, what is the value of $\left(\sqrt[4]{11}\right)^{6x+2}$? Express your answer as a fraction. -/
theorem mathd_algebra_275 (x : ℝ) (h : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (3 * x - 3) = 1 / 5) :
    ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * x + 2) = 121 / 25 := by
  have h_main : x = 1 - (4 * Real.log 5) / (3 * Real.log 11) := by
    have h₁ : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (3 * x - 3) = 1 / 5 := h
    have h₂ : Real.log (((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (3 * x - 3)) = Real.log (1 / 5) := by rw [h₁]
    have h₃ : Real.log (((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (3 * x - 3)) = (3 * x - 3) * Real.log ((11 : ℝ) ^ (1 / 4 : ℝ)) := by
      rw [Real.log_rpow (by positivity)]
      <;> ring_nf
    have h₄ : Real.log (1 / 5) = -Real.log 5 := by
      rw [Real.log_div (by norm_num) (by norm_num)]
      <;> simp [Real.log_one]
      <;> ring
    rw [h₃] at h₂
    rw [h₄] at h₂
    have h₅ : (3 * x - 3) * Real.log ((11 : ℝ) ^ (1 / 4 : ℝ)) = -Real.log 5 := by linarith
    have h₆ : Real.log ((11 : ℝ) ^ (1 / 4 : ℝ)) = (1 / 4 : ℝ) * Real.log 11 := by
      rw [Real.log_rpow (by positivity)]
      <;> ring_nf
    rw [h₆] at h₅
    have h₇ : (3 * x - 3) * ((1 / 4 : ℝ) * Real.log 11) = -Real.log 5 := by linarith
    have h₈ : 3 * x - 3 = (-4 * Real.log 5) / Real.log 11 := by
      have h₉ : Real.log 11 ≠ 0 := by
        exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
      field_simp at h₇ ⊢
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 11), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
    have h₉ : x = 1 - (4 * Real.log 5) / (3 * Real.log 11) := by
      have h₁₀ : 3 * x - 3 = (-4 * Real.log 5) / Real.log 11 := h₈
      have h₁₁ : 3 * x = 3 + (-4 * Real.log 5) / Real.log 11 := by linarith
      have h₁₂ : x = 1 + (-4 * Real.log 5) / (3 * Real.log 11) := by
        field_simp at h₁₁ ⊢
        nlinarith
      have h₁₃ : x = 1 - (4 * Real.log 5) / (3 * Real.log 11) := by
        have h₁₄ : Real.log 11 ≠ 0 := by
          exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
        field_simp at h₁₂ ⊢
        <;> ring_nf at *
        <;> nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 11), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
      exact h₁₃
    exact h₉
  
  have h_final : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * x + 2) = 121 / 25 := by
    rw [h_main]
    have h₁ : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * (1 - (4 * Real.log 5) / (3 * Real.log 11)) + 2) = 121 / 25 := by
      have h₂ : Real.log (((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * (1 - (4 * Real.log 5) / (3 * Real.log 11)) + 2)) = Real.log (121 / 25) := by
        have h₃ : Real.log (((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * (1 - (4 * Real.log 5) / (3 * Real.log 11)) + 2)) = (6 * (1 - (4 * Real.log 5) / (3 * Real.log 11)) + 2) * Real.log ((11 : ℝ) ^ (1 / 4 : ℝ)) := by
          rw [Real.log_rpow (by positivity)]
          <;> ring_nf
        rw [h₃]
        have h₄ : Real.log ((11 : ℝ) ^ (1 / 4 : ℝ)) = (1 / 4 : ℝ) * Real.log 11 := by
          rw [Real.log_rpow (by positivity)]
          <;> ring_nf
        rw [h₄]
        have h₅ : Real.log (121 / 25) = Real.log (121) - Real.log (25) := by
          rw [Real.log_div (by positivity) (by positivity)]
          <;> ring_nf
        rw [h₅]
        have h₆ : Real.log 121 = 2 * Real.log 11 := by
          have h₇ : Real.log 121 = Real.log (11 ^ 2) := by norm_num
          rw [h₇]
          have h₈ : Real.log (11 ^ 2) = 2 * Real.log 11 := by
            rw [Real.log_pow] <;> ring_nf <;> norm_num
          rw [h₈]
          <;> ring_nf
        have h₇ : Real.log 25 = 2 * Real.log 5 := by
          have h₈ : Real.log 25 = Real.log (5 ^ 2) := by norm_num
          rw [h₈]
          have h₉ : Real.log (5 ^ 2) = 2 * Real.log 5 := by
            rw [Real.log_pow] <;> ring_nf <;> norm_num
          rw [h₉]
          <;> ring_nf
        rw [h₆, h₇]
        ring_nf
        <;> field_simp
        <;> ring_nf
        <;> nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 11), Real.log_pos (by norm_num : (1 : ℝ) < 5),
          Real.log_pos (by norm_num : (1 : ℝ) < 5), Real.log_pos (by norm_num : (1 : ℝ) < 11)]
      have h₃ : Real.log (((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * (1 - (4 * Real.log 5) / (3 * Real.log 11)) + 2)) = Real.log (121 / 25) := by rw [h₂]
      have h₄ : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * (1 - (4 * Real.log 5) / (3 * Real.log 11)) + 2) = 121 / 25 := by
        apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
        linarith
      exact h₄
    simpa using h₁
  exact h_final
