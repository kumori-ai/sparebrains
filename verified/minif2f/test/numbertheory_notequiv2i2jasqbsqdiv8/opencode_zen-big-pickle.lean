import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have h1 := h 2 0
  have left : ∃ i j : ℤ, 2 = 2 * i ∧ 0 = 2 * j := ⟨1, 0, by norm_num, by norm_num⟩
  have right : ¬ ∃ k : ℤ, 2 ^ 2 + 0 ^ 2 = 8 * k := by
    rintro ⟨k, hk⟩
    norm_num at hk
    omega
  exact right (h1.mp left)
