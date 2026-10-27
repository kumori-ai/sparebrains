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
  rcases h₀ with ⟨ha, hb, hc⟩
  have habc_pos : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  rw [mul_add] at h₁
  rw [mul_add] at h₂
  rw [mul_add] at h₃
  have hsum : a * b + b * c + c * a = 242 := by
    calc
      a * b + b * c + c * a = ((a * b + a * c) + (b * c + b * a) + (c * a + c * b)) / 2 := by ring
      _ = (152 + 162 + 170) / 2 := by rw [h₁, h₂, h₃]
      _ = 242 := by norm_num
  have hab : a * b = 72 := by
    linarith
  have hbc : b * c = 90 := by
    linarith
  have hca : c * a = 80 := by
    linarith
  have hprod_sq : (a * b * c) ^ 2 = (720 : ℝ) ^ 2 := by
    calc
      (a * b * c) ^ 2 = (a * b) * (b * c) * (c * a) := by ring
      _ = 72 * 90 * 80 := by rw [hab, hbc, hca]
      _ = 518400 := by norm_num
      _ = (720 : ℝ) ^ 2 := by norm_num
  have hpos720 : 0 < (720 : ℝ) := by norm_num
  nlinarith
