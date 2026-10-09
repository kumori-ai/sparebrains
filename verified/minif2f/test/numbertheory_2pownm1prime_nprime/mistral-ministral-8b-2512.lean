import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) :
    Nat.Prime n := by
  have h2 : 2 ^ n - 1 > 1 := by
    exact Nat.Prime.one_lt h₁
  have h3 : Nat.Prime (2 ^ n - 1) → Nat.Prime n := by
    exact fun a => Nat.Prime.of_mersenne h₁
  exact h3 h₁