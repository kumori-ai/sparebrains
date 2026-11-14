import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have hleft : ∃ i j : ℤ, 2 = 2 * i ∧ 4 = 2 * j := by
    use 1, 2
    norm_num
  have hright : ¬ ∃ k : ℤ, 2 ^ 2 + 4 ^ 2 = 8 * k := by
    intro h
    rcases h with ⟨k, hk⟩
    norm_num at hk
    omega
  have hiff := h 2 4
  have hR := hiff.mp hleft
  exact hright hR
