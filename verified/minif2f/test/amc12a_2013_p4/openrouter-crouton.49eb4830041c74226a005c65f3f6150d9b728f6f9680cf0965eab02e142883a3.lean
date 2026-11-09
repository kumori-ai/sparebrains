import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of \[\frac{2^{2014}+2^{2012}}{2^{2014}-2^{2012}}?\]

$ \textbf{(A)}\ -1\qquad\textbf{(B)}\ 1\qquad\textbf{(C)}\ \frac{5}{3}\qquad\textbf{(D)}\ 2013\qquad\textbf{(E)}\ 2^{4024} $ -/
theorem amc12a_2013_p4 : (2 ^ 2014 + 2 ^ 2012) / (2 ^ 2014 - 2 ^ 2012) = (5 : ℝ) / 3 := by
  have ha : (2 : ℝ) ^ 2012 ≠ 0 := by positivity
  have h2014 : (2 : ℝ) ^ 2014 = 4 * (2 : ℝ) ^ 2012 := by
    rw [show (2014 : ℕ) = 2012 + 2 by norm_num, pow_add]
    ring
  have hnum : 4 * (2 : ℝ) ^ 2012 + (2 : ℝ) ^ 2012 = 5 * (2 : ℝ) ^ 2012 := by ring
  have hden : 4 * (2 : ℝ) ^ 2012 - (2 : ℝ) ^ 2012 = 3 * (2 : ℝ) ^ 2012 := by ring
  rw [h2014, hnum, hden, mul_div_mul_right _ _ ha]
