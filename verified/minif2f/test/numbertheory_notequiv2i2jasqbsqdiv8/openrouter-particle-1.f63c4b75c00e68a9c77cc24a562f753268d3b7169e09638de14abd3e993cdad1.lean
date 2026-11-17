import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have hiff := h 2 0
  have hL : ∃ i j : ℤ, (2 : ℤ) = 2 * i ∧ (0 : ℤ) = 2 * j := by
    refine ⟨1, 0, ?_, ?_⟩ <;> ring
  have hR : ¬ ∃ k : ℤ, (2 : ℤ) ^ 2 + (0 : ℤ) ^ 2 = 8 * k := by
    rintro ⟨k, hk⟩
    norm_num at hk
    omega
  exact hR (hiff.mp hL)
