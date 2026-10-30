import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of \[\frac{2^{2014}+2^{2012}}{2^{2014}-2^{2012}}?\]

$ \textbf{(A)}\ -1\qquad\textbf{(B)}\ 1\qquad\textbf{(C)}\ \frac{5}{3}\qquad\textbf{(D)}\ 2013\qquad\textbf{(E)}\ 2^{4024} $ -/
theorem amc12a_2013_p4 : (2 ^ 2014 + 2 ^ 2012) / (2 ^ 2014 - 2 ^ 2012) = (5 : ℝ) / 3 := by
  field_simp
  ring
