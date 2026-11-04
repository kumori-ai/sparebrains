import Mathlib

open scoped Nat
open scoped Real

/-- The sum of the two $ 5$-digit numbers $ AMC10$ and $ AMC12$ is $ 123422$. What is $ A+{}M+{}C$?

$ \textbf{(A)}\ 10 \qquad
\textbf{(B)}\ 11 \qquad
\textbf{(C)}\ 12 \qquad
\textbf{(D)}\ 13 \qquad
\textbf{(E)}\ 14$ -/
theorem amc12a_2003_p5 (A M C : ℕ) (h₀ : A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9)
    (h₁ : Nat.ofDigits 10 [0, 1, C, M, A] + Nat.ofDigits 10 [2, 1, C, M, A] = 123422) :
    A + M + C = 14 := by
  rcases h₀ with ⟨hA, hM, hC⟩
  have hsum : 100 * A + 10 * M + C = 617 := by
    simp [Nat.ofDigits] at h₁
    omega
  have hA6 : A = 6 := by
    omega
  have hMC : 10 * M + C = 17 := by
    omega
  have hM1 : M = 1 := by
    omega
  have hC7 : C = 7 := by
    omega
  omega
