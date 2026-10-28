import Mathlib

open scoped Nat
open scoped Real

/--
Which of the following is equivalent to $$(2+3)(2^2+3^2)(2^4+3^4)(2^8+3^8)(2^{16}+3^{16})(2^{32}+3^{32})(2^{64}+3^{64})?$$

$\textbf{(A) }3^{127}+2^{127} \qquad \textbf{(B) }3^{127}+2^{127}+2\cdot 3^{63}+3\cdot 2^{63} \qquad \textbf{(C) }3^{128}-2^{128} \qquad \textbf{(D) }3^{128}+2^{128} \qquad \textbf{(E) }5^{127}$ -/
theorem amc12a_2021_p9 : ∏ k ∈ Finset.range 7, (2 ^ 2 ^ k + 3 ^ 2 ^ k) = 3 ^ 128 - 2 ^ 128 := by
  have h1 : (2 ^ 2 ^ 0 + 3 ^ 2 ^ 0) * (2 ^ 2 ^ 1 + 3 ^ 2 ^ 1) * (2 ^ 2 ^ 2 + 3 ^ 2 ^ 2) * (2 ^ 2 ^ 3 + 3 ^ 2 ^ 3) * (2 ^ 2 ^ 4 + 3 ^ 2 ^ 4) * (2 ^ 2 ^ 5 + 3 ^ 2 ^ 5) * (2 ^ 2 ^ 6 + 3 ^ 2 ^ 6) = 3 ^ 128 - 2 ^ 128 := by
    norm_num [Finset.prod_range_succ]
  simp_all [Finset.prod_range_succ, pow_succ, pow_zero, add_zero, mul_add, add_mul, mul_assoc]
  <;> ring_nf at h1 ⊢
  <;> omega
