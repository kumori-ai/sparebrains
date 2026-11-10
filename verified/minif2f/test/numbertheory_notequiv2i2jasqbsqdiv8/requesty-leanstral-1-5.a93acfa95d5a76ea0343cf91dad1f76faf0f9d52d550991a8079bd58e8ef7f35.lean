import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have hleft : ∃ i j : ℤ, (2 : ℤ) = 2 * i ∧ (0 : ℤ) = 2 * j := by
    refine ⟨1, 0, ?_, ?_⟩
    · ring
    · ring
  have hright := (h 2 0).mp hleft
  rcases hright with ⟨k, hk⟩
  omega
