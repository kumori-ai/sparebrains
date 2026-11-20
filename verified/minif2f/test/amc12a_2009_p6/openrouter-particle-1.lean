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
  rw [← Real.rpow_mul (x := 2) (y := m) (z := 2 * n) (hx := by norm_num)]
  rw [← Real.rpow_mul (x := 3) (y := n) (z := m) (hx := by norm_num)]
  rw [show m * (2 * n) = 2 * (m * n) by ring]
  rw [show n * m = m * n by ring]
  rw [Real.rpow_mul (x := 2) (y := 2) (z := m * n) (hx := by norm_num)]
  rw [← Real.mul_rpow (x := (2 : ℝ) ^ (2 : ℝ)) (y := 3) (z := m * n)
    (hx := by norm_num [Real.rpow_natCast]) (hy := by norm_num)]
  have hbase : (2 : ℝ) ^ (2 : ℝ) * 3 = 12 := by
    norm_num [Real.rpow_natCast]
  rw [hbase]
