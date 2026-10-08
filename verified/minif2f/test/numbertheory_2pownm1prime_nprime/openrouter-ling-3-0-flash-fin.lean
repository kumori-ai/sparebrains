import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) :
    Nat.Prime n := by
  -- We prove the contrapositive: if n is not prime, then 2^n - 1 is not prime.
  exact Nat.Prime.of_mersenne h₁