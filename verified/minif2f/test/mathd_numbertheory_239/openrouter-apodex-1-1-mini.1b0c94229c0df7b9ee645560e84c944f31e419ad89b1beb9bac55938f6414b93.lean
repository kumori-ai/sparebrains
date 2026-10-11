import Mathlib

open scoped Nat
open scoped Real

/--
Determine the modulo 4 remainder of the following sum: $$ 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12. $$ -/
theorem mathd_numbertheory_239 : (∑ k ∈ Finset.Icc 1 12, k) % 4 = 2 := by
  decide
