import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) :
    Nat.Prime n := by
  have hprime : Nat.Prime n := by
    have hprime2 : Nat.Prime 2 := Nat.prime_two
    exact Nat.Prime.of_mersenne h₁
  exact hprime
