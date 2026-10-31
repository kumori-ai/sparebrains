import Mathlib

open scoped Nat
open scoped Real

/-- What is the units digit of the product of all of the odd integers between 0 and 12? -/
theorem mathd_numbertheory_343 : (∏ k ∈ Finset.range 6, (2 * k + 1)) % 10 = 5 := by
  norm_num
