import Mathlib

open scoped Nat
open scoped Real

theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778 (r : ℝ)
    (h₀ : r ^ ((1 : ℝ) / 3) + 1 / r ^ ((1 : ℝ) / 3) = 3)
    (h₁ : 0 < r) : r ^ 3 + 1 / r ^ 3 = 5778 := by
  have h₂ : (r ^ ((1 : ℝ) / 3)) + 1 / (r ^ ((1 : ℝ) / 3)) = 3 := by
    have h₂₁ : (r : ℝ) ^ ((1 : ℝ) / 3) + 1 / (r : ℝ) ^ ((1 : ℝ) / 3) = 3 := by
      simpa using h₀
    exact h₂₁
  
  have h₃ : (r ^ ((1 : ℝ) / 3)) ^ 3 + 1 / (r ^ ((1 : ℝ) / 3)) ^ 3 = 18 := by
    have h₃₁ : 0 < (r : ℝ) ^ ((1 : ℝ) / 3) := by positivity
    have h₃₂ : (r : ℝ) ^ ((1 : ℝ) / 3) + 1 / (r : ℝ) ^ ((1 : ℝ) / 3) = 3 := h₂
    have h₃₃ : ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 1 / ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 18 := by
      have h₃₄ : ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 1 / ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 1 / ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := rfl
      have h₃₅ : ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 1 / ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 18 := by
        have h₃₆ : ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 1 / ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 1 / ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := rfl
        -- Use the identity (x + 1/x)^3 = x^3 + 1/x^3 + 3(x + 1/x)
        have h₃₇ : ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 1 / ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 18 := by
          have h₃₈ : ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 1 / ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (((r : ℝ) ^ ((1 : ℝ) / 3)) + 1 / ((r : ℝ) ^ ((1 : ℝ) / 3))) ^ 3 - 3 * (((r : ℝ) ^ ((1 : ℝ) / 3)) + 1 / ((r : ℝ) ^ ((1 : ℝ) / 3))) := by
            have h₃₉ : 0 < (r : ℝ) ^ ((1 : ℝ) / 3) := by positivity
            field_simp [h₃₉.ne']
            <;> ring_nf
            <;> field_simp [h₃₉.ne']
            <;> ring_nf
          rw [h₃₈]
          rw [h₃₂]
          norm_num
        exact h₃₇
      exact h₃₅
    exact h₃₃
  
  have h₄ : r + 1 / r = 18 := by
    have h₄₁ : (r ^ ((1 : ℝ) / 3)) ^ 3 = r := by
      have h₄₂ : 0 < r := h₁
      have h₄₃ : (r : ℝ) > 0 := by exact_mod_cast h₄₂
      have h₄₄ : (r : ℝ) ^ ((1 : ℝ) / 3) > 0 := by positivity
      have h₄₅ : ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = r := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul] <;> ring_nf <;> norm_num <;>
          (try positivity) <;>
          (try linarith)
        <;>
        simp_all [Real.rpow_def_of_pos]
        <;>
        field_simp
        <;>
        ring_nf
        <;>
        norm_num
        <;>
        linarith
      exact h₄₅
    have h₄₆ : 1 / (r ^ ((1 : ℝ) / 3)) ^ 3 = 1 / r := by
      have h₄₇ : 0 < r := h₁
      have h₄₈ : 0 < (r : ℝ) ^ ((1 : ℝ) / 3) := by positivity
      have h₄₉ : (r : ℝ) ^ ((1 : ℝ) / 3) > 0 := by positivity
      have h₅₀ : ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = r := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul] <;> ring_nf <;> norm_num <;>
          (try positivity) <;>
          (try linarith)
        <;>
        simp_all [Real.rpow_def_of_pos]
        <;>
        field_simp
        <;>
        ring_nf
        <;>
        norm_num
        <;>
        linarith
      calc
        1 / (r ^ ((1 : ℝ) / 3)) ^ 3 = 1 / ((r : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by norm_cast
        _ = 1 / r := by
          rw [h₅₀]
          <;> field_simp
          <;> ring_nf
          <;> norm_num
          <;> linarith
    have h₄₁₀ : (r ^ ((1 : ℝ) / 3)) ^ 3 + 1 / (r ^ ((1 : ℝ) / 3)) ^ 3 = 18 := h₃
    have h₄₁₁ : r + 1 / r = 18 := by
      calc
        r + 1 / r = ((r ^ ((1 : ℝ) / 3)) ^ 3) + 1 / ((r ^ ((1 : ℝ) / 3)) ^ 3) := by
          linarith
        _ = 18 := by rw [h₄₁₀]
    exact h₄₁₁
  
  have h₅ : (r + 1 / r) ^ 3 = 5832 := by
    rw [h₄]
    <;> norm_num
  
  have h₆ : r ^ 3 + 1 / r ^ 3 + 3 * (r + 1 / r) = 5832 := by
    have h₆₁ : (r + 1 / r) ^ 3 = r ^ 3 + 1 / r ^ 3 + 3 * (r + 1 / r) := by
      have h₆₂ : 0 < r := h₁
      have h₆₃ : 0 < r ^ 2 := by positivity
      have h₆₄ : 0 < r ^ 3 := by positivity
      field_simp [h₆₂.ne', h₆₃.ne', h₆₄.ne']
      ring_nf
      <;>
      nlinarith [sq_nonneg (r - 1), sq_nonneg (r + 1), sq_nonneg (r ^ 2 - 1)]
    linarith
  
  have h₇ : r ^ 3 + 1 / r ^ 3 = 5778 := by
    have h₇₁ : r ^ 3 + 1 / r ^ 3 + 3 * (r + 1 / r) = 5832 := h₆
    have h₇₂ : r + 1 / r = 18 := h₄
    have h₇₃ : 3 * (r + 1 / r) = 54 := by
      rw [h₇₂]
      <;> norm_num
    have h₇₄ : r ^ 3 + 1 / r ^ 3 + 54 = 5832 := by linarith
    have h₇₅ : r ^ 3 + 1 / r ^ 3 = 5778 := by linarith
    exact h₇₅
  
  exact h₇
