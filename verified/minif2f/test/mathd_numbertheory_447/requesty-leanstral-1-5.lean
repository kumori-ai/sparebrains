import Mathlib

open scoped Nat
open scoped Real

/-- What is the sum of the units digits of all the multiples of $3$ between $0$ and $50$? -/
theorem mathd_numbertheory_447 :
    ∑ k ∈ Finset.filter (fun x => 3 ∣ x) (Finset.Icc 1 49), k % 10 = 78 := by
  decide
