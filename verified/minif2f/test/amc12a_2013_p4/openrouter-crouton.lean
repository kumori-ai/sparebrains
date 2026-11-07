import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of \[\frac{2^{2014}+2^{2012}}{2^{2014}-2^{2012}}?\]

$ \textbf{(A)}\ -1\qquad\textbf{(B)}\ 1\qquad\textbf{(C)}\ \frac{5}{3}\qquad\textbf{(D)}\ 2013\qquad\textbf{(E)}\ 2^{4024} $ -/
theorem amc12a_2013_p4 : (2 ^ 2014 + 2 ^ 2012) / (2 ^ 2014 - 2 ^ 2012) = (5 : ℝ) / 3 := by
  have h2014 : (2 : ℝ) ^ 2014 = 4 * (2 : ℝ) ^ 2012 := by
    rw [show (2014 : ℕ) = 2012 + 2 from rfl, pow_add, show (2 : ℝ) ^ 2 = 4 by norm_num,
      mul_comm ((2 : ℝ) ^ 2012) 4]
  have hx : (2 : ℝ) ^ 2012 ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [h2014]
  have key : ∀ x : ℝ, x ≠ 0 → (4 * x + x) / (4 * x - x) = (5 : ℝ) / 3 := by
    intro x hx
    have hn : 4 * x + x = 5 * x := by ring
    have hd : 4 * x - x = 3 * x := by ring
    rw [hn, hd, mul_div_mul_right _ _ hx]
  exact key _ hx
