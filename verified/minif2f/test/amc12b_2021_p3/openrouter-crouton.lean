import Mathlib

open scoped Nat
open scoped Real

/-- Suppose $$2+\frac{1}{1+\frac{1}{2+\frac{2}{3+x}}}=\frac{144}{53}.$$ What is the value of $x?$

$\textbf{(A) }\frac34 \qquad \textbf{(B) }\frac78 \qquad \textbf{(C) }\frac{14}{15} \qquad \textbf{(D) }\frac{37}{38} \qquad \textbf{(E) }\frac{52}{53}$ -/
theorem amc12b_2021_p3 (x : ℝ) (h₀ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53) : x = 3 / 4 := by
  by_cases h1 : (3 : ℝ) + x = 0
  · rw [h1] at h₀
    norm_num at h₀
  by_cases h2 : (2 : ℝ) + 2 / (3 + x) = 0
  · rw [h2] at h₀
    norm_num at h₀
  by_cases h3 : (1 : ℝ) + 1 / (2 + 2 / (3 + x)) = 0
  · rw [h3] at h₀
    norm_num at h₀
  have e1 : 1 / (1 + 1 / (2 + 2 / (3 + x))) = 38 / 53 := by linarith
  have e2 : 1 + 1 / (2 + 2 / (3 + x)) = 53 / 38 := by
    rw [div_eq_iff h3] at e1
    linarith
  have e3 : 1 / (2 + 2 / (3 + x)) = 15 / 38 := by linarith
  have e4 : 2 + 2 / (3 + x) = 38 / 15 := by
    rw [div_eq_iff h2] at e3
    linarith
  have e5 : 2 / (3 + x) = 8 / 15 := by linarith
  have e6 : 3 + x = 15 / 4 := by
    rw [div_eq_iff h1] at e5
    linarith
  linarith
