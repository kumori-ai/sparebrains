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
  have h2pos : (0 : ℝ) ≤ 2 := by norm_num
  have h3pos : (0 : ℝ) ≤ 3 := by norm_num
  calc p ^ (2 * n) * q ^ m
      = (2 ^ m) ^ (2 * n) * (3 ^ n) ^ m := by rw [h₀, h₁]
    _ = 2 ^ (m * (2 * n)) * 3 ^ (n * m) := by
        rw [← Real.rpow_mul h2pos, ← Real.rpow_mul h3pos]
    _ = 2 ^ (2 * (m * n)) * 3 ^ (m * n) := by
        have e1 : m * (2 * n) = 2 * (m * n) := by ring
        have e2 : n * m = m * n := by ring
        rw [e1, e2]
    _ = (2 ^ (2 : ℝ)) ^ (m * n) * 3 ^ (m * n) := by
        rw [Real.rpow_mul h2pos]
    _ = ((2 ^ (2 : ℝ)) * 3) ^ (m * n) := by
        rw [Real.mul_rpow (by positivity) h3pos]
    _ = 12 ^ (m * n) := by
        have hbase : (2 : ℝ) ^ (2 : ℝ) * 3 = 12 := by
          have h : (2 : ℝ) ^ (2 : ℝ) = 4 := by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            norm_num
          rw [h]
          norm_num
        rw [hbase]
