import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of \[\frac{2^{2014}+2^{2012}}{2^{2014}-2^{2012}}?\]

$ \textbf{(A)}\ -1\qquad\textbf{(B)}\ 1\qquad\textbf{(C)}\ \frac{5}{3}\qquad\textbf{(D)}\ 2013\qquad\textbf{(E)}\ 2^{4024} $ -/
theorem amc12a_2013_p4 : (2 ^ 2014 + 2 ^ 2012) / (2 ^ 2014 - 2 ^ 2012) = (5 : ℝ) / 3 := by
  have hpow : (2:ℝ) ^ 2014 = 4 * (2:ℝ) ^ 2012 := by
    change (2:ℝ) ^ (2012 + 2) = 4 * (2:ℝ) ^ 2012
    rw [pow_add]
    norm_num
    ring
  have hden : (2:ℝ) ^ 2014 - (2:ℝ) ^ 2012 ≠ 0 := by
    rw [hpow]
    have h : 4 * (2:ℝ) ^ 2012 - (2:ℝ) ^ 2012 = 3 * (2:ℝ) ^ 2012 := by ring
    rw [h]
    have hpos : 0 < (3:ℝ) * (2:ℝ) ^ 2012 := by positivity
    exact ne_of_gt hpos
  field_simp [hden]
  ring_nf
