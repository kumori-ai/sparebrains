import Mathlib

open scoped Nat
open scoped Real

/-- What is the units digit of the sum of the squares of the first nine positive integers? -/
theorem mathd_numbertheory_3 : (∑ x ∈ Finset.range 10, (x + 1) ^ 2) % 10 = 5 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
