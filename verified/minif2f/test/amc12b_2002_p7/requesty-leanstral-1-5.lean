import Mathlib

open scoped Nat
open scoped Real

/--
The product of three consecutive positive integers is $ 8$ times their sum. What is the sum of their squares?

$ \textbf{(A)}\ 50 \qquad
\textbf{(B)}\ 77 \qquad
\textbf{(C)}\ 110 \qquad
\textbf{(D)}\ 149 \qquad
\textbf{(E)}\ 194$ -/
theorem amc12b_2002_p7 (a b c : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : b = a + 1) (h₂ : c = b + 1)
    (h₃ : a * b * c = 8 * (a + b + c)) : a ^ 2 + (b ^ 2 + c ^ 2) = 77 := by
  rcases h₀ with ⟨ha, hb, hc⟩
  zify [ha, hb, hc, h₁, h₂, h₃] at *
  nlinarith
