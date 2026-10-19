import Mathlib

open scoped Nat
open scoped Real

/--
Suppose that $ P={}2^m$ and $ Q={}3^n$. Which of the following is equal to $ 12^{mn}$ for every pair of integers $ (m,n)$?

$ \textbf{(A)}\ P^2Q \qquad
\textbf{(B)}\ P^nQ^m \qquad
\textbf{(C)}\ P^nQ^{2m} \qquad
\textbf{(D)}\ P^{2m}Q^n \qquad
\textbf{(E)}\ P^{2n}Q^m$ -/
theorem amc12a_2009_p6 (m n p q : ℝ) (h₀ : p = 2 ^ m) (h₁ : q = 3 ^ n) :
    p ^ (2 * n) * q ^ m = 12 ^ (m * n) := by
  rw [h₀, h₁]
  have h2pos : (2 : ℝ) ≥ 0 := by norm_num
  have h3pos : (3 : ℝ) ≥ 0 := by norm_num
  have h4pos : (4 : ℝ) ≥ 0 := by norm_num
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have h3 : 0 ≤ (3 : ℝ) := by norm_num
  have h4 : 0 ≤ (4 : ℝ) := by norm_num
  have hexp1 : m * ((2 : ℝ) * n) = 2 * m * n := by ring
  have hexp2 : n * m = m * n := by ring
  have hexp3 : 2 * m * n = 2 * (m * n) := by ring
  have h_eq : (2 : ℝ) ^ (2 * m * n) = ((2 : ℝ) ^ 2) ^ (m * n) := by
    calc
      (2 : ℝ) ^ (2 * m * n) = (2 : ℝ) ^ (2 * (m * n)) := by rw [hexp3]
      _ = ((2 : ℝ) ^ 2) ^ (m * n) := by
        have h2pos : (0 : ℝ) ≤ 2 := by norm_num
        have h_pow_eq : (2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by
          calc
            (2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) := by norm_num
            _ = (2 : ℝ) ^ (2 : ℕ) := by rw [Real.rpow_natCast]
        rw [Real.rpow_mul h2pos (2 : ℝ) (m * n), h_pow_eq]
  calc
    ((2 : ℝ) ^ m) ^ ((2 : ℝ) * n) * ((3 : ℝ) ^ n) ^ m
        = ((2 : ℝ) ^ (m * ((2 : ℝ) * n))) * ((3 : ℝ) ^ (n * m)) := by
          rw [Real.rpow_mul h2 m ((2 : ℝ) * n), Real.rpow_mul h3 n m]
    _ = ((2 : ℝ) ^ (2 * m * n)) * ((3 : ℝ) ^ (m * n)) := by rw [hexp1, hexp2]
    _ = (((2 : ℝ) ^ 2) ^ (m * n)) * ((3 : ℝ) ^ (m * n)) := by rw [h_eq]
    _ = ((4 : ℝ) ^ (m * n)) * ((3 : ℝ) ^ (m * n)) := by norm_num
    _ = ((4 : ℝ) * (3 : ℝ)) ^ (m * n) := by
      exact Eq.symm (Real.mul_rpow h4 h3)
    _ = (12 : ℝ) ^ (m * n) := by norm_num