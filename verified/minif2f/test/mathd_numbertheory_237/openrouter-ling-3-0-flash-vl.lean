import Mathlib

open scoped Nat
open scoped Real

/-- What is the modulo $6$ remainder of the sum $1+2+3+4+\dots+98+99+100?$ -/
theorem mathd_numbertheory_237 : (∑ k ∈ Finset.range 101, k) % 6 = 4 := by
  calc (∑ k ∈ Finset.range 101, k) % 6 = (101 * 100 / 2) % 6 := by simp [Finset.sum_range_id]
    _ = 5050 % 6 := by norm_num
    _ = 4 := by norm_num
