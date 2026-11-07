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
  have ha : 0 < a := h₀.1
  have hb : 0 < b := h₀.2.1
  have hc : 0 < c := h₀.2.2
  have h1' : a * b + a * c = 152 := by linear_combination h₁
  have h2' : b * c + b * a = 162 := by linear_combination h₂
  have h3' : c * a + c * b = 170 := by linear_combination h₃
  have hab : a * b = 72 := by linarith
  have hbc : b * c = 90 := by linarith
  have hca : c * a = 80 := by linarith
  have hpos : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have hsq : (a * b * c) ^ 2 = 720 ^ 2 := by
    have h : (a * b * c) ^ 2 = (a * b) * (b * c) * (c * a) := by ring
    rw [h, hab, hbc, hca]
    norm_num
  have hfactor : (a * b * c - 720) * (a * b * c + 720) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · linarith
