import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have h24 := h 2 4
  have hleft : ∃ i j : ℤ, (2 : ℤ) = 2 * i ∧ (4 : ℤ) = 2 * j := by
    exact ⟨1, 2, by norm_num, by norm_num⟩
  rcases (h24.mp hleft) with ⟨k, hk⟩
  norm_num at hk
  omega
