import Mathlib

open scoped Nat
open scoped Real

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  have h_base : 11 ∣ (10 : ℤ) ^ 0 - (-1 : ℤ) ^ 0 := by
    norm_num
    <;>
    decide
  
  have h_inductive_step : ∀ (k : ℕ), 11 ∣ (10 : ℤ) ^ k - (-1 : ℤ) ^ k → 11 ∣ (10 : ℤ) ^ (k + 1) - (-1 : ℤ) ^ (k + 1) := by
    intro k ih
    have h₁ : (10 : ℤ) ^ (k + 1) - (-1 : ℤ) ^ (k + 1) = 10 * ((10 : ℤ) ^ k - (-1 : ℤ) ^ k) + 11 * (-1 : ℤ) ^ k := by
      ring_nf
      <;> simp [pow_succ, mul_assoc]
      <;> ring_nf
      <;> norm_num
      <;> linarith
    rw [h₁]
    -- Use the fact that if a number divides two terms, it divides their sum
    have h₂ : (11 : ℤ) ∣ 10 * ((10 : ℤ) ^ k - (-1 : ℤ) ^ k) := by
      -- Since 11 divides (10^k - (-1)^k), it divides any multiple of it
      exact dvd_mul_of_dvd_right ih 10
    have h₃ : (11 : ℤ) ∣ 11 * (-1 : ℤ) ^ k := by
      -- 11 divides 11 * (-1)^k trivially
      use (-1 : ℤ) ^ k
      <;> ring_nf
      <;> norm_num
    -- Combine the two divisibility results
    exact dvd_add h₂ h₃
  
  have h_main : 11 ∣ (10 : ℤ) ^ n - (-1 : ℤ) ^ n := by
    have h : ∀ n : ℕ, 11 ∣ (10 : ℤ) ^ n - (-1 : ℤ) ^ n := by
      intro n
      induction n with
      | zero =>
        simpa using h_base
      | succ k ih =>
        apply h_inductive_step
        exact ih
    exact h n
  
  exact h_main
