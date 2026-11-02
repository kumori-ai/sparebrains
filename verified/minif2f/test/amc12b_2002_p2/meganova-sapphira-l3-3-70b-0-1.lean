import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of
\[ (3x -{} 2)(4x +{} 1) -{} (3x -{} 2)4x +{} 1\]when $ x ={} 4$?

$ \textbf{(A)}\ 0 \qquad \textbf{(B)}\ 1 \qquad \textbf{(C)}\ 10 \qquad \textbf{(D)}\ 11 \qquad \textbf{(E)}\ 12$ -/
theorem amc12b_2002_p2 (x : ℤ) (h₀ : x = 4) :
    (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11 := by
  subst h₀
  ring
