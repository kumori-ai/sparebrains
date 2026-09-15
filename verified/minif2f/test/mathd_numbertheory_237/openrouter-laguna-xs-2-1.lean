import Mathlib

open scoped Nat
open scoped Real

/-- What is the modulo $6$ remainder of the sum $1+2+3+4+\dots+98+99+100?$ -/
theorem mathd_numbertheory_237 : (∑ k ∈ Finset.range 101, k) % 6 = 4 := by
  have h_sum : ∑ k ∈ Finset.range 101, k = 101 * 100 / 2 := by
    simpa [Finset.sum_range_id]
  simpa [h_sum] using by norm_num
