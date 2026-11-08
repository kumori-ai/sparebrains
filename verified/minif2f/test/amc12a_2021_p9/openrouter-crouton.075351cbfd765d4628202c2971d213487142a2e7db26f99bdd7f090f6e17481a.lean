import Mathlib

open scoped Nat
open scoped Real

/--
Which of the following is equivalent to $$(2+3)(2^2+3^2)(2^4+3^4)(2^8+3^8)(2^{16}+3^{16})(2^{32}+3^{32})(2^{64}+3^{64})?$$

$\textbf{(A) }3^{127}+2^{127} \qquad \textbf{(B) }3^{127}+2^{127}+2\cdot 3^{63}+3\cdot 2^{63} \qquad \textbf{(C) }3^{128}-2^{128} \qquad \textbf{(D) }3^{128}+2^{128} \qquad \textbf{(E) }5^{127}$ -/
theorem amc12a_2021_p9 : ∏ k ∈ Finset.range 7, (2 ^ 2 ^ k + 3 ^ 2 ^ k) = 3 ^ 128 - 2 ^ 128 := by
  have key : ∀ n : ℕ, ((3 : ℤ) - 2) * ∏ k ∈ Finset.range n, ((2 : ℤ) ^ 2 ^ k + (3 : ℤ) ^ 2 ^ k)
      = (3 : ℤ) ^ 2 ^ n - (2 : ℤ) ^ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ]
      have hstep : ((3 : ℤ) - 2) * ((∏ k ∈ Finset.range n, ((2 : ℤ) ^ 2 ^ k + (3 : ℤ) ^ 2 ^ k))
          * ((2 : ℤ) ^ 2 ^ n + (3 : ℤ) ^ 2 ^ n))
          = ((3 : ℤ) ^ 2 ^ n - (2 : ℤ) ^ 2 ^ n) * ((2 : ℤ) ^ 2 ^ n + (3 : ℤ) ^ 2 ^ n) := by
        rw [← ih]; ring
      rw [hstep]
      have h3 : (3 : ℤ) ^ 2 ^ (n + 1) = ((3 : ℤ) ^ 2 ^ n) ^ 2 := by
        have e : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
        rw [e, pow_mul]
      have h2 : (2 : ℤ) ^ 2 ^ (n + 1) = ((2 : ℤ) ^ 2 ^ n) ^ 2 := by
        have e : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
        rw [e, pow_mul]
      rw [h3, h2]
      ring
  have hle : (2 : ℕ) ^ 128 ≤ 3 ^ 128 := Nat.pow_le_pow_left (by norm_num) 128
  have hcast : ((∏ k ∈ Finset.range 7, (2 ^ 2 ^ k + 3 ^ 2 ^ k) : ℕ) : ℤ)
      = ((3 ^ 128 - 2 ^ 128 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle]
    push_cast
    have h := key 7
    rw [show ((3 : ℤ) - 2) = 1 by norm_num, one_mul] at h
    exact h
  exact_mod_cast hcast
