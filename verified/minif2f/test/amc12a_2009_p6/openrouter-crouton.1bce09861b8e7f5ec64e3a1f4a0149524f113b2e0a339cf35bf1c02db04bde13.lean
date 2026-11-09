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
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have h22 : ((2 : ℝ) ^ (2 : ℝ)) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  calc ((2 : ℝ) ^ m) ^ (2 * n) * ((3 : ℝ) ^ n) ^ m
      = (2 : ℝ) ^ (m * (2 * n)) * (3 : ℝ) ^ (n * m) := by
        rw [← Real.rpow_mul h2, ← Real.rpow_mul h3]
    _ = (2 : ℝ) ^ (2 * (m * n)) * (3 : ℝ) ^ (m * n) := by
        rw [show m * (2 * n) = 2 * (m * n) by ring, show n * m = m * n by ring]
    _ = ((2 : ℝ) ^ (2 : ℝ)) ^ (m * n) * (3 : ℝ) ^ (m * n) := by
        rw [Real.rpow_mul h2]
    _ = (4 : ℝ) ^ (m * n) * (3 : ℝ) ^ (m * n) := by rw [h22]
    _ = ((4 : ℝ) * 3) ^ (m * n) := by
        rw [Real.mul_rpow h4 h3]
    _ = (12 : ℝ) ^ (m * n) := by
        rw [show (4 : ℝ) * 3 = 12 by norm_num]
