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
  subst h₁
  subst h₂
  have h3z : (a : ℤ) * ((a : ℤ) + 1) * ((a : ℤ) + 1 + 1)
      = 8 * ((a : ℤ) + ((a : ℤ) + 1) + ((a : ℤ) + 1 + 1)) := by
    exact_mod_cast h₃
  have hfactor : ((a : ℤ) + 1) * ((a : ℤ) * ((a : ℤ) + 2) - 24) = 0 := by
    linear_combination h3z
  have ha_pos : (0 : ℤ) < (a : ℤ) := by exact_mod_cast h₀.1
  have hA : (a : ℤ) = 4 := by
    have h24 : (a : ℤ) * ((a : ℤ) + 2) = 24 := by
      rcases mul_eq_zero.mp hfactor with h | h
      · linarith
      · linarith
    have hfact2 : ((a : ℤ) - 4) * ((a : ℤ) + 6) = 0 := by
      linear_combination h24
    rcases mul_eq_zero.mp hfact2 with h | h
    · linarith
    · linarith
  have ha4 : a = 4 := by exact_mod_cast hA
  rw [ha4]
  norm_num
