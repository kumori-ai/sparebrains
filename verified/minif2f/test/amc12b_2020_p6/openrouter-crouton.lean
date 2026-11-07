import Mathlib

open scoped Nat
open scoped Real

/-- For all integers $n \geq 9,$ the value of
$$\frac{(n+2)!-(n+1)!}{n!}$$
is always which of the following?

$\textbf{(A) } \text{a multiple of }4 \qquad \textbf{(B) } \text{a multiple of }10 \qquad \textbf{(C) } \text{a prime number} \\ \textbf{(D) } \text{a perfect square} \qquad \textbf{(E) } \text{a perfect cube}$ -/
theorem amc12b_2020_p6 (n : ℕ) (h₀ : 9 ≤ n) : ∃ x : ℕ, (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!) / n ! := by
  use n + 1
  have hn : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have e2 : ((n + 1)! : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
    have h : (n + 1)! = (n + 1) * n ! := Nat.factorial_succ n
    rw [h]
    push_cast
    ring
  have e1 : ((n + 2)! : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) * (n ! : ℝ) := by
    have h : (n + 2)! = (n + 2) * (n + 1) * n ! := by
      rw [show n + 2 = (n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      ring
    rw [h]
    push_cast
    ring
  rw [e1, e2]
  push_cast
  rw [eq_div_iff hn]
  ring
