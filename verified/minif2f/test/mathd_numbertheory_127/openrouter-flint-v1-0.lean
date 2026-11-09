import Mathlib

open scoped Nat
open scoped Real

/-- Find the remainder when $1 + 2 + 2^2 + 2^3 + \dots + 2^{100}$ is divided by 7. -/
theorem mathd_numbertheory_127 : (∑ k ∈ Finset.range 101, 2 ^ k) % 7 = 3 := by
  simp [Finset.sum_range_succ, Nat.pow_succ, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_eq_of_lt]
