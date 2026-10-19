import Mathlib

open scoped Nat
open scoped Real

/-- For all integers $n \geq 9,$ the value of
$$\frac{(n+2)!-(n+1)!}{n!}$$
is always which of the following?

$\textbf{(A) } \text{a multiple of }4 \qquad \textbf{(B) } \text{a multiple of }10 \qquad \textbf{(C) } \text{a prime number} \\ \textbf{(D) } \text{a perfect square} \qquad \textbf{(E) } \text{a perfect cube}$ -/
theorem amc12b_2020_p6 (n : ℕ) (h₀ : 9 ≤ n) : ∃ x : ℕ, (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!) / n ! := by
  have h_main : ∃ x : ℕ, (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!) / n ! := by
    use n + 1
    have h₁ : ((n + 2)! - (n + 1)!) / n ! = (n + 1 : ℝ) ^ 2 := by
      have h₂ : n ≥ 9 := by linarith
      have h₃ : (n + 2)! = (n + 2) * (n + 1) * n ! := by
        simp [Nat.factorial_succ, Nat.mul_assoc]
        <;> ring
        <;> simp [Nat.factorial_succ, Nat.mul_assoc]
        <;> ring
      have h₄ : (n + 1)! = (n + 1) * n ! := by
        simp [Nat.factorial_succ, Nat.mul_assoc]
        <;> ring
      rw [h₃, h₄]
      cases n with
      | zero => contradiction
      | succ n =>
        cases n with
        | zero => contradiction
        | succ n =>
          cases n with
          | zero => contradiction
          | succ n =>
            cases n with
            | zero => contradiction
            | succ n =>
              cases n with
              | zero => contradiction
              | succ n =>
                cases n with
                | zero => contradiction
                | succ n =>
                  cases n with
                  | zero => contradiction
                  | succ n =>
                    simp [Nat.div_eq_of_lt, Nat.factorial_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                    <;> ring_nf at *
                    <;> field_simp [Nat.factorial_succ, Nat.mul_assoc]
                    <;> ring_nf
                    <;> norm_num
                    <;>
                    (try omega) <;>
                    (try
                      {
                        simp_all [Nat.factorial_succ, Nat.mul_assoc]
                        <;> ring_nf at *
                        <;> field_simp [Nat.factorial_succ, Nat.mul_assoc]
                        <;> ring_nf
                        <;> norm_num
                        <;>
                        (try omega)
                        <;>
                        (try nlinarith)
                      }) <;>
                    (try
                      {
                        simp_all [Nat.factorial_succ, Nat.mul_assoc]
                        <;> ring_nf at *
                        <;> field_simp [Nat.factorial_succ, Nat.mul_assoc]
                        <;> ring_nf
                        <;> norm_num
                        <;>
                        (try omega)
                        <;>
                        (try nlinarith)
                      })
    simp_all
    <;> norm_num
    <;> ring_nf
    <;> field_simp [Nat.factorial_succ, Nat.mul_assoc]
    <;> ring_nf
    <;> norm_num
    <;>
    (try omega) <;>
    (try nlinarith)
  
  exact h_main
