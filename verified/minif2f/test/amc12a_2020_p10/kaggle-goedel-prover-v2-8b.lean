import Mathlib

open scoped Nat
open scoped Real

/--
There is a unique positive integer $n$ larger than 1 such that \[\log_2{(\log_{16}{n})} = \log_4{(\log_4{n})}.\]
What is the sum of the digits of $n?$

$\textbf{(A) } 4 \qquad \textbf{(B) } 7 \qquad \textbf{(C) } 8 \qquad \textbf{(D) } 11 \qquad \textbf{(E) } 13$ -/
theorem amc12a_2020_p10 (n : ℕ) (h₀ : 1 < n)
    (h₁ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n)) :
    (Nat.digits 10 n).sum = 13 := by
  have h₂ : n = 256 := by
    have h₂₁ : (n : ℝ) > 1 := by exact_mod_cast h₀
    have h₂₂ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n) := h₁
    have h₂₃ : Real.logb 16 n = Real.log n / Real.log 16 := by
      rw [Real.logb]
      <;> simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> field_simp
      <;> ring
    have h₂₄ : Real.logb 4 n = Real.log n / Real.log 4 := by
      rw [Real.logb]
      <;> simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> field_simp
      <;> ring
    have h₂₅ : Real.logb 2 (Real.logb 16 n) = Real.log (Real.logb 16 n) / Real.log 2 := by
      rw [Real.logb]
      <;> simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> field_simp
      <;> ring
    have h₂₆ : Real.logb 4 (Real.logb 4 n) = Real.log (Real.logb 4 n) / Real.log 4 := by
      rw [Real.logb]
      <;> simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> field_simp
      <;> ring
    have h₂₇ : Real.log 4 = 2 * Real.log 2 := by
      have h₂₇₁ : Real.log 4 = Real.log (2 ^ 2) := by norm_num
      rw [h₂₇₁]
      have h₂₇₂ : Real.log (2 ^ 2) = 2 * Real.log 2 := by
        rw [Real.log_pow]
        <;> norm_num
      rw [h₂₇₂]
      <;> ring
    have h₂₈ : Real.log 16 = 4 * Real.log 2 := by
      have h₂₈₁ : Real.log 16 = Real.log (2 ^ 4) := by norm_num
      rw [h₂₈₁]
      have h₂₈₂ : Real.log (2 ^ 4) = 4 * Real.log 2 := by
        rw [Real.log_pow]
        <;> norm_num
      rw [h₂₈₂]
      <;> ring
    have h₂₉ : Real.logb 16 n = (Real.log n / Real.log 2) / 4 := by
      rw [h₂₃, h₂₈]
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring
    have h₃₀ : Real.logb 4 n = (Real.log n / Real.log 2) / 2 := by
      rw [h₂₄, h₂₇]
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring
    have h₃₁ : Real.logb 2 (Real.logb 16 n) = Real.log ((Real.log n / Real.log 2) / 4) / Real.log 2 := by
      rw [h₂₅, h₂₉]
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring
    have h₃₂ : Real.logb 4 (Real.logb 4 n) = Real.log ((Real.log n / Real.log 2) / 2) / (2 * Real.log 2) := by
      rw [h₂₆, h₃₀, h₂₇]
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring
    have h₃₃ : Real.log ((Real.log n / Real.log 2) / 4) / Real.log 2 = Real.log ((Real.log n / Real.log 2) / 2) / (2 * Real.log 2) := by
      linarith
    have h₃₄ : 2 * Real.log ((Real.log n / Real.log 2) / 4) = Real.log ((Real.log n / Real.log 2) / 2) := by
      have h₃₄₁ : Real.log 2 > 0 := Real.log_pos (by norm_num)
      have h₃₄₂ : Real.log 2 ≠ 0 := by linarith
      field_simp [h₃₄₂, Real.log_mul, Real.log_rpow, Real.log_pow] at h₃₃ ⊢
      <;> ring_nf at h₃₃ ⊢ <;> nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have h₃₅ : Real.log ((Real.log n / Real.log 2) / 4) = Real.log (Real.log n / Real.log 2) - Real.log 4 := by
      have h₃₅₁ : Real.log ((Real.log n / Real.log 2) / 4) = Real.log (Real.log n / Real.log 2) - Real.log 4 := by
        rw [Real.log_div (by
          have h₃₅₂ : Real.log n / Real.log 2 ≠ 0 := by
            have h₃₅₃ : Real.log n > 0 := Real.log_pos (by
              have h₃₅₄ : (n : ℝ) > 1 := by exact_mod_cast h₀
              exact_mod_cast h₃₅₄)
            have h₃₅₄ : Real.log 2 > 0 := Real.log_pos (by norm_num)
            positivity
          have h₃₅₅ : (4 : ℝ) > 0 := by norm_num
          positivity
        ) (by positivity)]
        <;> simp [Real.log_mul, Real.log_rpow, Real.log_pow]
        <;> ring
      rw [h₃₅₁]
    have h₃₆ : Real.log ((Real.log n / Real.log 2) / 2) = Real.log (Real.log n / Real.log 2) - Real.log 2 := by
      have h₃₆₁ : Real.log ((Real.log n / Real.log 2) / 2) = Real.log (Real.log n / Real.log 2) - Real.log 2 := by
        rw [Real.log_div (by
          have h₃₆₂ : Real.log n / Real.log 2 ≠ 0 := by
            have h₃₆₃ : Real.log n > 0 := Real.log_pos (by
              have h₃₆₄ : (n : ℝ) > 1 := by exact_mod_cast h₀
              exact_mod_cast h₃₆₄)
            have h₃₆₄ : Real.log 2 > 0 := Real.log_pos (by norm_num)
            positivity
          have h₃₆₅ : (2 : ℝ) > 0 := by norm_num
          positivity
        ) (by positivity)]
        <;> simp [Real.log_mul, Real.log_rpow, Real.log_pow]
        <;> ring
      rw [h₃₆₁]
    have h₃₇ : 2 * (Real.log (Real.log n / Real.log 2) - Real.log 4) = Real.log (Real.log n / Real.log 2) - Real.log 2 := by
      rw [h₃₅, h₃₆] at h₃₄
      exact h₃₄
    have h₃₈ : Real.log 4 = 2 * Real.log 2 := by
      have h₃₈₁ : Real.log 4 = Real.log (2 ^ 2) := by norm_num
      rw [h₃₈₁]
      have h₃₈₂ : Real.log (2 ^ 2) = 2 * Real.log 2 := by
        rw [Real.log_pow]
        <;> norm_num
      rw [h₃₈₂]
      <;> ring
    have h₃₉ : 2 * (Real.log (Real.log n / Real.log 2) - (2 * Real.log 2)) = Real.log (Real.log n / Real.log 2) - Real.log 2 := by
      rw [h₃₈] at h₃₇
      exact h₃₇
    have h₄₀ : Real.log (Real.log n / Real.log 2) - 3 * Real.log 2 = 0 := by
      linarith
    have h₄₁ : Real.log (Real.log n / Real.log 2) = 3 * Real.log 2 := by
      linarith
    have h₄₂ : Real.log n / Real.log 2 = 8 := by
      have h₄₂₁ : Real.log (Real.log n / Real.log 2) = 3 * Real.log 2 := h₄₁
      have h₄₂₂ : Real.log n / Real.log 2 > 0 := by
        have h₄₂₃ : Real.log n > 0 := Real.log_pos (by
          have h₄₂₄ : (n : ℝ) > 1 := by exact_mod_cast h₀
          exact_mod_cast h₄₂₄)
        have h₄₂₄ : Real.log 2 > 0 := Real.log_pos (by norm_num)
        positivity
      have h₄₂₃ : Real.log (Real.log n / Real.log 2) = 3 * Real.log 2 := h₄₁
      have h₄₂₄ : Real.log n / Real.log 2 = 8 := by
        have h₄₂₅ : Real.log (Real.log n / Real.log 2) = Real.log 8 := by
          rw [h₄₂₃]
          have h₄₂₆ : Real.log 8 = 3 * Real.log 2 := by
            have h₄₂₇ : Real.log 8 = Real.log (2 ^ 3) := by norm_num
            rw [h₄₂₇]
            have h₄₂₈ : Real.log (2 ^ 3) = 3 * Real.log 2 := by
              rw [Real.log_pow]
              <;> norm_num
            rw [h₄₂₈]
            <;> ring
          rw [h₄₂₆]
        have h₄₂₆ : Real.log n / Real.log 2 > 0 := h₄₂₂
        have h₄₂₇ : Real.log (Real.log n / Real.log 2) = Real.log 8 := h₄₂₅
        have h₄₂₈ : Real.log n / Real.log 2 = 8 := by
          apply Real.log_injOn_pos (Set.mem_Ioi.mpr h₄₂₆) (Set.mem_Ioi.mpr (by norm_num))
          rw [h₄₂₇]
          <;> simp [Real.log_pow]
          <;> ring
          <;> norm_num
        exact h₄₂₈
      exact h₄₂₄
    have h₄₃ : Real.log n = 8 * Real.log 2 := by
      have h₄₃₁ : Real.log n / Real.log 2 = 8 := h₄₂
      have h₄₃₂ : Real.log 2 > 0 := Real.log_pos (by norm_num)
      field_simp [h₄₃₂.ne'] at h₄₃₁ ⊢
      <;> nlinarith
    have h₄₄ : (n : ℝ) = 256 := by
      have h₄₄₁ : Real.log n = Real.log 256 := by
        have h₄₄₂ : Real.log 256 = 8 * Real.log 2 := by
          have h₄₄₃ : Real.log 256 = Real.log (2 ^ 8) := by norm_num
          rw [h₄₄₃]
          have h₄₄₄ : Real.log (2 ^ 8) = 8 * Real.log 2 := by
            rw [Real.log_pow]
            <;> norm_num
          rw [h₄₄₄]
          <;> ring
        linarith
      have h₄₄₅ : Real.log n = Real.log 256 := h₄₄₁
      have h₄₄₆ : (n : ℝ) = 256 := by
        apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
        linarith
      exact h₄₄₆
    have h₄₅ : n = 256 := by
      norm_cast at h₄₄ ⊢
      <;> linarith
    exact h₄₅
  
  have h₃ : (Nat.digits 10 n).sum = 13 := by
    rw [h₂]
    <;> norm_num [Nat.digits_zero, Nat.div_eq_of_lt]
    <;> rfl
  
  exact h₃
