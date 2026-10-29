import Mathlib

open scoped Nat
open scoped Real

/--
For how many positive integers $ m$ does there exist at least one positive integer $ n$ such that $ m\cdot n \le m +{} n$?

$ \textbf{(A)}\ 4 \qquad \textbf{(B)}\ 6 \qquad \textbf{(C)}\ 9 \qquad \textbf{(D)}\ 12 \qquad \textbf{(E)}$ infinitely many -/
theorem amc12a_2002_p6 (n : ℕ) (h₀ : 0 < n) : ∃ m, m > n ∧ ∃ p, m * p ≤ m + p := by
  use n + 1
  constructor
  · omega
  · use 1
    omega
