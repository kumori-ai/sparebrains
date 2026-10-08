import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) :
    Nat.Prime n := by
  have : 2 ^ n - 1 > 1 := by
    exact Nat.Prime.one_lt h₁
  exact Nat.Prime.of_mersenne h₁