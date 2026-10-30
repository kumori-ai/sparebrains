import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have h2 := h 2 0
  rcases h2 with ⟨hforward, hbackward⟩
  have even_2_0 : ∃ i j : ℤ, (2 : ℤ) = 2 * i ∧ (0 : ℤ) = 2 * j := by
    refine ⟨1, 0, ?_, ?_⟩
    · ring
    · ring
  have hdiv8 := hforward even_2_0
  rcases hdiv8 with ⟨k, hk⟩
  have hcalc : (2 : ℤ) ^ 2 + (0 : ℤ) ^ 2 = 4 := by ring
  rw [hcalc] at hk
  omega
