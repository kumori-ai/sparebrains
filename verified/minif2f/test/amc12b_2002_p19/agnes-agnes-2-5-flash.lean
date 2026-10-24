import Mathlib

open scoped Nat
open scoped Real

/--
If $ a$, $ b$, and $ c$ are positive real numbers such that $ a(b +{} c) ={} 152$, $ b(c +{} a) ={} 162$, and $ c(a +{} b) ={} 170$, then abc is

$ \textbf{(A)}\ 672 \qquad
\textbf{(B)}\ 688 \qquad
\textbf{(C)}\ 704 \qquad
\textbf{(D)}\ 720 \qquad
\textbf{(E)}\ 750$ -/
theorem amc12b_2002_p19 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : a * (b + c) = 152)
    (h₂ : b * (c + a) = 162) (h₃ : c * (a + b) = 170) : a * b * c = 720 := by
  have h₄ : a * b + a * c = 152 := by linarith
  have h₅ : b * c + a * b = 162 := by linarith
  have h₆ : a * c + b * c = 170 := by linarith
  have h₇ : a * b = 72 := by linarith
  have h₈ : b * c = 90 := by linarith
  have h₉ : a * c = 80 := by linarith
  have h₁₀ : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact h₀.1
    exact h₀.2.1
    exact h₀.2.2
  have h₁₁ : (a * b * c) ^ 2 = 720 ^ 2 := by
    calc
      (a * b * c) ^ 2 = (a * b) * (b * c) * (a * c) := by ring
      _ = 72 * 90 * 80 := by rw [h₇, h₈, h₉]
      _ = 720 ^ 2 := by norm_num
  have h₁₂ : a * b * c = 720 := by
    have h₁₃ : 0 < a * b * c := h₁₀
    nlinarith
  exact h₁₂
