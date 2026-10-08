import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) :
    Nat.Prime n := by
  -- First show 1 < n
  have h₁' : n ≠ 1 := by
    intro h
    rw [h] at h₁
    aesop
  -- Actually, Nat.Prime 1 is false, so h₁ : Nat.Prime (2^1 - 1) = Nat.Prime 1 gives False
  -- So we need to show n ≠ 1 first
  exact Nat.Prime.of_mersenne h₁