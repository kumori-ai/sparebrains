import Mathlib

open scoped Nat
open scoped Real

/-- For all integers $n \geq 9,$ the value of
$$\frac{(n+2)!-(n+1)!}{n!}$$
is always which of the following?

$\textbf{(A) } \text{a multiple of }4 \qquad \textbf{(B) } \text{a multiple of }10 \qquad \textbf{(C) } \text{a prime number} \\ \textbf{(D) } \text{a perfect square} \qquad \textbf{(E) } \text{a perfect cube}$ -/
theorem amc12b_2020_p6 (n : ℕ) (h₀ : 9 ≤ n) : ∃ x : ℕ, (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!) / n ! := by
  use n + 1
  have h1nat : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := Nat.factorial_succ n
  have h2nat : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := by
    have h := Nat.factorial_succ (n + 1)
    rwa [show n + 1 + 1 = n + 2 by omega] at h
  have h1 : (Nat.factorial (n + 1) : ℝ) = (n + 1) * (Nat.factorial n : ℝ) := by
    exact_mod_cast h1nat
  have h2 : (Nat.factorial (n + 2) : ℝ) = (n + 2) * (Nat.factorial (n + 1) : ℝ) := by
    exact_mod_cast h2nat
  have hn : (Nat.factorial n : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    exact ne_of_gt hpos
  rw [h2, h1]
  push_cast
  field_simp [hn]
  ring
