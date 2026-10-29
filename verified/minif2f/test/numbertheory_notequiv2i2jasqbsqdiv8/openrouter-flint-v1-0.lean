import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have h2 := h 2 4
  have hnot : ¬ ((∃ i j, (2 : ℤ) = 2 * i ∧ (4 : ℤ) = 2 * j) ↔ ∃ k, (2 : ℤ) ^ 2 + (4 : ℤ) ^ 2 = 8 * k) := by
    intro hEq
    have hLeft : ∃ i j, (2 : ℤ) = 2 * i ∧ (4 : ℤ) = 2 * j := by
      refine ⟨1, 2, ?_⟩
      norm_num
    have hRight : ∃ k, (2 : ℤ) ^ 2 + (4 : ℤ) ^ 2 = 8 * k := hEq.mp hLeft
    rcases hRight with ⟨k, hk⟩
    have hsum : (2 : ℤ) ^ 2 + (4 : ℤ) ^ 2 = 8 * k := hk
    norm_num at hsum
    omega
  exact hnot h2
