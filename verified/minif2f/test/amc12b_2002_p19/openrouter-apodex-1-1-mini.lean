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
  have h₄ : a * b + a * c = 152 := by linarith [h₁]
  have h₅ : b * c + a * b = 162 := by linarith [h₂]
  have h₆ : a * c + b * c = 170 := by linarith [h₃]
  have h₇ : a * b + b * c + a * c = 242 := by linarith [h₄, h₅, h₆]
  have h₈ : a * b = 72 := by linarith [h₆, h₇]
  have h₉ : b * c = 90 := by linarith [h₄, h₇]
  have h₁₀ : a * c = 80 := by linarith [h₅, h₇]
  have h₁₁ : (a * b * c) ^ 2 = 518400 := by
    calc
      (a * b * c) ^ 2 = (a * b) * (b * c) * (a * c) := by ring
      _ = 72 * 90 * 80 := by rw [h₈, h₉, h₁₀]
      _ = 518400 := by norm_num
  have h₁₂ : 0 < a * b * c := mul_pos (mul_pos h₀.1 h₀.2.1) h₀.2.2
  have h₁₃ : a * b * c = 720 := by
    have h₁₄ : (a * b * c) ^ 2 = 720 ^ 2 := by
      rw [h₁₁]
      norm_num
    have h₁₅ : 0 < (720 : ℝ) := by norm_num
    have h₁₆ : a * b * c = 720 ∨ a * b * c = -720 := by
      apply eq_or_eq_neg_of_sq_eq_sq
      rw [h₁₄]
    cases h₁₆ with
    | inl h => exact h
    | inr h => linarith [h₁₂]
  exact h₁₃
