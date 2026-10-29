import Mathlib

open scoped Nat
open scoped Real

/-- For all integers $n \geq 9,$ the value of
$$\frac{(n+2)!-(n+1)!}{n!}$$
is always which of the following?

$\textbf{(A) } \text{a multiple of }4 \qquad \textbf{(B) } \text{a multiple of }10 \qquad \textbf{(C) } \text{a prime number} \\ \textbf{(D) } \text{a perfect square} \qquad \textbf{(E) } \text{a perfect cube}$ -/
theorem amc12b_2020_p6 (n : ℕ) (h₀ : 9 ≤ n) : ∃ x : ℕ, (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!) / n ! := by
  refine ⟨n+1, ?_⟩
  have hpos : (n ! : ℝ) ≠ 0 := by
    exact mod_cast (Nat.factorial_pos n).ne.symm
  field_simp [hpos]
  rw [Nat.factorial_succ (n+1), Nat.factorial_succ n]
  push_cast
  ring
