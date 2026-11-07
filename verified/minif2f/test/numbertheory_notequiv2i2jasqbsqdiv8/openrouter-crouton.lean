import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have hiff := h 2 0
  have lhs : ∃ i j, (2 : ℤ) = 2 * i ∧ (0 : ℤ) = 2 * j := ⟨1, 0, by norm_num, by norm_num⟩
  obtain ⟨k, hk⟩ := hiff.mp lhs
  have hk2 : (4 : ℤ) = 8 * k := by
    calc (4 : ℤ) = (2 : ℤ) ^ 2 + (0 : ℤ) ^ 2 := by norm_num
    _ = 8 * k := hk
  omega
