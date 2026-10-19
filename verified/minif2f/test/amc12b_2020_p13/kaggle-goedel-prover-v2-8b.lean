import Mathlib

open scoped Nat
open scoped Real

/-- Which of the following is the value of $\sqrt{\log_2{6}+\log_3{6}}?$

$\textbf{(A) } 1 \qquad\textbf{(B) } \sqrt{\log_5{6}} \qquad\textbf{(C) } 2 \qquad\textbf{(D) } \sqrt{\log_2{3}}+\sqrt{\log_3{2}} \qquad\textbf{(E) } \sqrt{\log_2{6}}+\sqrt{\log_3{6}}$ -/
theorem amc12b_2020_p13 :
    Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) =
      Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
  have h₁ : Real.log 6 = Real.log 2 + Real.log 3 := by
    have h₁ : Real.log 6 = Real.log (2 * 3) := by norm_num
    rw [h₁]
    have h₂ : Real.log (2 * 3) = Real.log 2 + Real.log 3 := by
      rw [Real.log_mul (by norm_num) (by norm_num)]
    rw [h₂]
    <;>
    norm_num
  
  have h₂ : Real.log 6 / Real.log 2 = 1 + Real.log 3 / Real.log 2 := by
    have h₂ : Real.log 6 / Real.log 2 = (Real.log 2 + Real.log 3) / Real.log 2 := by rw [h₁]
    rw [h₂]
    have h₃ : (Real.log 2 + Real.log 3) / Real.log 2 = 1 + Real.log 3 / Real.log 2 := by
      have h₄ : Real.log 2 ≠ 0 := by
        -- Prove that the logarithm of 2 is not zero
        have h₅ : Real.log 2 > 0 := Real.log_pos (by norm_num)
        linarith
      field_simp [h₄]
      <;> ring
      <;> field_simp [h₄]
      <;> ring
    rw [h₃]
    <;>
    norm_num
  
  have h₃ : Real.log 6 / Real.log 3 = 1 + Real.log 2 / Real.log 3 := by
    have h₃ : Real.log 6 / Real.log 3 = (Real.log 2 + Real.log 3) / Real.log 3 := by rw [h₁]
    rw [h₃]
    have h₄ : (Real.log 2 + Real.log 3) / Real.log 3 = 1 + Real.log 2 / Real.log 3 := by
      have h₅ : Real.log 3 ≠ 0 := by
        have h₅₁ : Real.log 3 > 0 := Real.log_pos (by norm_num)
        linarith
      field_simp [h₅]
      <;> ring
      <;> field_simp [h₅]
      <;> ring
    rw [h₄]
    <;>
    norm_num
  
  have h₄ : Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 = 2 + Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 := by
    rw [h₂, h₃]
    <;> ring_nf
    <;> field_simp [Real.log_mul, Real.log_pow]
    <;> ring_nf
    <;> linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  
  have h₅ : Real.log 3 / Real.log 2 > 0 := by
    have h₅ : Real.log 3 > 0 := Real.log_pos (by norm_num)
    have h₆ : Real.log 2 > 0 := Real.log_pos (by norm_num)
    have h₇ : Real.log 3 / Real.log 2 > 0 := by positivity
    exact h₇
  
  have h₆ : Real.log 2 / Real.log 3 > 0 := by
    have h₆ : Real.log 2 > 0 := Real.log_pos (by norm_num)
    have h₇ : Real.log 3 > 0 := Real.log_pos (by norm_num)
    have h₈ : Real.log 2 / Real.log 3 > 0 := by positivity
    exact h₈
  
  have h₇ : Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3) = 1 := by
    have h₇ : Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3) = Real.sqrt ((Real.log 3 / Real.log 2) * (Real.log 2 / Real.log 3)) := by
      rw [← Real.sqrt_mul] <;>
      (try positivity) <;>
      (try linarith) <;>
      (try ring_nf) <;>
      (try field_simp) <;>
      (try nlinarith)
    rw [h₇]
    have h₈ : (Real.log 3 / Real.log 2 : ℝ) * (Real.log 2 / Real.log 3) = 1 := by
      have h₈₁ : Real.log 2 ≠ 0 := by
        have h₈₂ : Real.log 2 > 0 := Real.log_pos (by norm_num)
        linarith
      have h₈₂ : Real.log 3 ≠ 0 := by
        have h₈₃ : Real.log 3 > 0 := Real.log_pos (by norm_num)
        linarith
      field_simp [h₈₁, h₈₂]
      <;> ring_nf
      <;> field_simp [h₈₁, h₈₂]
      <;> linarith
    rw [h₈]
    <;> simp [Real.sqrt_one]
    <;> norm_num
  
  have h₈ : (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 = 2 + Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 := by
    have h₈ : 0 ≤ Real.sqrt (Real.log 3 / Real.log 2) := Real.sqrt_nonneg _
    have h₉ : 0 ≤ Real.sqrt (Real.log 2 / Real.log 3) := Real.sqrt_nonneg _
    have h₁₀ : 0 ≤ Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3) := by positivity
    have h₁₁ : (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 = (Real.sqrt (Real.log 3 / Real.log 2)) ^ 2 + (Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 + 2 * (Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3)) := by
      nlinarith [sq_nonneg (Real.sqrt (Real.log 3 / Real.log 2) - Real.sqrt (Real.log 2 / Real.log 3))]
    rw [h₁₁]
    have h₁₂ : (Real.sqrt (Real.log 3 / Real.log 2)) ^ 2 = Real.log 3 / Real.log 2 := by
      rw [Real.sq_sqrt] <;> positivity
    have h₁₃ : (Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 = Real.log 2 / Real.log 3 := by
      rw [Real.sq_sqrt] <;> positivity
    rw [h₁₂, h₁₃, h₇]
    <;> ring_nf
    <;> field_simp [h₅, h₆]
    <;> nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  
  have h₉ : Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 = (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 := by
    rw [h₄]
    rw [h₈]
    <;>
    ring_nf at *
    <;>
    nlinarith
  
  have h₁₀ : Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
    have h₁₀ : Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 = (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 := by
      rw [h₉]
    rw [h₁₀]
    have h₁₁ : 0 ≤ Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
      positivity
    rw [Real.sqrt_sq h₁₁]
    <;>
    ring_nf
    <;>
    nlinarith
  
  rw [h₁₀]
  <;>
  ring_nf
  <;>
  nlinarith
