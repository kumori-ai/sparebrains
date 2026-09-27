import Mathlib

open scoped Nat
open scoped Real

/-- How many integers between 15 and 85 are divisible by 20? -/
theorem mathd_numbertheory_12 :
    Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by
  decide
