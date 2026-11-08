import Mathlib

open scoped Nat
open scoped Real

/-- What is the modulo $6$ remainder of the sum $1+2+3+4+\dots+98+99+100?$ -/
theorem mathd_numbertheory_237 : (∑ k ∈ Finset.range 101, k) % 6 = 4 := by
  have h := Finset.sum_range_id_mul_two 101
  have hsum : (∑ k ∈ Finset.range 101, k) = 5050 := by omega
  rw [hsum]
