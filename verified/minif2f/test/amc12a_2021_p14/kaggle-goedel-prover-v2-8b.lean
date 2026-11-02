import Mathlib

open scoped Nat
open scoped Real

/--
What is the value of $$\left(\sum_{k=1}^{20} \log_{5^k} 3^{k^2}\right)\cdot\left(\sum_{k=1}^{100} \log_{9^k} 25^k\right)?$$

$\textbf{(A) }21 \qquad \textbf{(B) }100\log_5 3 \qquad \textbf{(C) }200\log_3 5 \qquad \textbf{(D) }2,200\qquad \textbf{(E) }21,000$ -/
theorem amc12a_2021_p14 :
    (∑ k ∈ Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) *
        ∑ k ∈ Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k) =
      21000 := by
  -- First sum: ∑ log_{5^k}(3^{k^2})
  let sum1 := ∑ k ∈ Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)
  · have h_sum₁ : (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), Real.logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ))) = 210 * (Real.log 3 / Real.log 5) := by
      have h₁ : ∀ (k : ℕ), k ∈ Finset.Icc (1 : ℕ) (20 : ℕ) → Real.logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ)) = (k : ℝ) * Real.log 3 / Real.log 5 := by
        intro k hk
        have h₂ : k ∈ Finset.Icc (1 : ℕ) (20 : ℕ) := hk
        have h₃ : 1 ≤ k ∧ k ≤ 20 := by simpa using h₂
        have h₄ : (k : ℝ) ≥ 1 := by exact_mod_cast h₃.1
        have h₅ : (k : ℝ) ≤ 20 := by exact_mod_cast h₃.2
        have h₆ : Real.logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ)) = Real.log ((3 : ℝ) ^ k ^ (2 : ℕ)) / Real.log ((5 : ℝ) ^ k) := by
          rw [Real.logb]
          <;> simp [Real.log_rpow, Real.log_pow, h₄, h₅]
          <;> field_simp
          <;> ring
        rw [h₆]
        have h₇ : Real.log ((3 : ℝ) ^ k ^ (2 : ℕ)) = (k ^ (2 : ℕ) : ℝ) * Real.log 3 := by
          rw [Real.log_pow]
          <;> simp [Real.log_pow, h₄, h₅]
          <;> ring_nf
          <;> field_simp
          <;> ring_nf
        have h₈ : Real.log ((5 : ℝ) ^ k) = (k : ℝ) * Real.log 5 := by
          rw [Real.log_pow]
          <;> simp [Real.log_pow, h₄, h₅]
          <;> ring_nf
          <;> field_simp
          <;> ring_nf
        rw [h₇, h₈]
        have h₉ : (k ^ (2 : ℕ) : ℝ) = (k : ℝ) ^ 2 := by
          norm_cast
          <;> ring_nf
        rw [h₉]
        have h₁₀ : ((k : ℝ) ^ 2 * Real.log 3) / ((k : ℝ) * Real.log 5) = (k : ℝ) * Real.log 3 / Real.log 5 := by
          have h₁₁ : (k : ℝ) ≠ 0 := by
            have h₁₂ : (k : ℝ) ≥ 1 := by exact_mod_cast h₃.1
            linarith
          have h₁₃ : Real.log 5 ≠ 0 := by
            have h₁₄ : Real.log 5 > 0 := Real.log_pos (by norm_num)
            linarith
          field_simp [h₁₁, h₁₃]
          <;> ring_nf
          <;> field_simp [h₁₁, h₁₃]
          <;> ring_nf
          <;> field_simp [h₁₁, h₁₃]
          <;> linarith
        rw [h₁₀]
      calc
        (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), Real.logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ))) = ∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), ((k : ℝ) * Real.log 3 / Real.log 5 : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [h₁ k hk]
        _ = ∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), ((k : ℝ) * Real.log 3 / Real.log 5 : ℝ) := rfl
        _ = (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), ((k : ℝ) : ℝ)) * (Real.log 3 / Real.log 5) := by
          have h₂ : ∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), ((k : ℝ) * Real.log 3 / Real.log 5 : ℝ) = (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), ((k : ℝ) : ℝ)) * (Real.log 3 / Real.log 5) := by
            calc
              ∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), ((k : ℝ) * Real.log 3 / Real.log 5 : ℝ) = ∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), ((k : ℝ) : ℝ) * (Real.log 3 / Real.log 5) := by
                apply Finset.sum_congr rfl
                intro k hk
                field_simp [Real.log_mul, Real.log_pow, Real.log_rpow, Real.log_pow]
                <;> ring_nf
                <;> field_simp [Real.log_mul, Real.log_pow, Real.log_rpow, Real.log_pow]
                <;> ring_nf
              _ = (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), ((k : ℝ) : ℝ)) * (Real.log 3 / Real.log 5) := by
                rw [Finset.sum_mul]
                <;> field_simp [Real.log_mul, Real.log_pow, Real.log_rpow, Real.log_pow]
                <;> ring_nf
                <;> field_simp [Real.log_mul, Real.log_pow, Real.log_rpow, Real.log_pow]
                <;> ring_nf
          rw [h₂]
        _ = (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), ((k : ℝ) : ℝ)) * (Real.log 3 / Real.log 5) := by rfl
        _ = 210 * (Real.log 3 / Real.log 5) := by
          have h₃ : ∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), ((k : ℝ) : ℝ) = 210 := by
            norm_num [Finset.sum_Icc_succ_top, Finset.sum_range_succ, Finset.sum_range_zero]
            <;> rfl
          rw [h₃]
          <;> ring_nf
          <;> field_simp [Real.log_mul, Real.log_pow, Real.log_rpow, Real.log_pow]
          <;> ring_nf
          <;> field_simp [Real.log_mul, Real.log_pow, Real.log_rpow, Real.log_pow]
          <;> linarith
    
    have h_sum₂ : (∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), Real.logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k)) = 100 * (Real.log 5 / Real.log 3) := by
      have h₁ : ∀ (k : ℕ), k ∈ Finset.Icc (1 : ℕ) (100 : ℕ) → Real.logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k) = Real.log 5 / Real.log 3 := by
        intro k hk
        have h₂ : k ∈ Finset.Icc (1 : ℕ) (100 : ℕ) := hk
        have h₃ : 1 ≤ k ∧ k ≤ 100 := by simpa using h₂
        have h₄ : (k : ℝ) ≥ 1 := by exact_mod_cast h₃.1
        have h₅ : (k : ℝ) ≤ 100 := by exact_mod_cast h₃.2
        have h₆ : Real.logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k) = Real.log ((25 : ℝ) ^ k) / Real.log ((9 : ℝ) ^ k) := by
          rw [Real.logb]
          <;> simp [Real.log_rpow, Real.log_pow, h₄, h₅]
          <;> field_simp
          <;> ring
        rw [h₆]
        have h₇ : Real.log ((25 : ℝ) ^ k) = (k : ℝ) * Real.log 25 := by
          rw [Real.log_pow]
          <;> simp [Real.log_pow, h₄, h₅]
          <;> ring_nf
          <;> field_simp
          <;> ring_nf
        have h₈ : Real.log ((9 : ℝ) ^ k) = (k : ℝ) * Real.log 9 := by
          rw [Real.log_pow]
          <;> simp [Real.log_pow, h₄, h₅]
          <;> ring_nf
          <;> field_simp
          <;> ring_nf
        rw [h₇, h₈]
        have h₉ : Real.log 25 = 2 * Real.log 5 := by
          have h₉₁ : Real.log 25 = Real.log (5 ^ 2) := by norm_num
          rw [h₉₁]
          have h₉₂ : Real.log (5 ^ 2) = 2 * Real.log 5 := by
            rw [Real.log_pow]
            <;> norm_num
          rw [h₉₂]
        have h₁₀ : Real.log 9 = 2 * Real.log 3 := by
          have h₁₀₁ : Real.log 9 = Real.log (3 ^ 2) := by norm_num
          rw [h₁₀₁]
          have h₁₀₂ : Real.log (3 ^ 2) = 2 * Real.log 3 := by
            rw [Real.log_pow]
            <;> norm_num
          rw [h₁₀₂]
        rw [h₉, h₁₀]
        have h₁₁ : (k : ℝ) ≠ 0 := by
          have h₁₂ : (k : ℝ) ≥ 1 := by exact_mod_cast h₃.1
          linarith
        have h₁₃ : (2 * Real.log 5 : ℝ) ≠ 0 := by
          have h₁₄ : Real.log 5 > 0 := Real.log_pos (by norm_num)
          linarith
        have h₁₅ : (2 * Real.log 3 : ℝ) ≠ 0 := by
          have h₁₆ : Real.log 3 > 0 := Real.log_pos (by norm_num)
          linarith
        field_simp [h₁₁, h₁₃, h₁₅]
        <;> ring_nf
        <;> field_simp [h₁₁, h₁₃, h₁₅]
        <;> ring_nf
        <;> field_simp [h₁₁, h₁₃, h₁₅]
        <;> linarith
      calc
        (∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), Real.logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k)) = ∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), (Real.log 5 / Real.log 3 : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [h₁ k hk]
        _ = ∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), (Real.log 5 / Real.log 3 : ℝ) := rfl
        _ = 100 * (Real.log 5 / Real.log 3) := by
          have h₂ : ∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), (Real.log 5 / Real.log 3 : ℝ) = 100 * (Real.log 5 / Real.log 3) := by
            simp [Finset.sum_const, Finset.card_range]
            <;> norm_num
          rw [h₂]
        _ = 100 * (Real.log 5 / Real.log 3) := by rfl
    
    have h_final : (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), Real.logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ))) * ∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), Real.logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k) = (21000 : ℝ) := by
      rw [h_sum₁, h_sum₂]
      have h₁ : Real.log 5 ≠ 0 := by
        have h₂ : Real.log 5 > 0 := Real.log_pos (by norm_num)
        linarith
      have h₂ : Real.log 3 ≠ 0 := by
        have h₃ : Real.log 3 > 0 := Real.log_pos (by norm_num)
        linarith
      have h₃ : Real.log 5 / Real.log 3 ≠ 0 := by positivity
      have h₄ : Real.log 3 / Real.log 5 ≠ 0 := by positivity
      field_simp [h₁, h₂, h₃, h₄]
      <;> ring_nf
      <;> field_simp [h₁, h₂, h₃, h₄]
      <;> norm_num
      <;> linarith
    
    rw [h_final]
    <;> norm_num
    <;> linarith
  -- Second sum: ∑ log_{9^k}(25^k)