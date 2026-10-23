import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have h₁ := h 2 4
  have h₂ : (∃ i j : ℤ, (2 : ℤ) = 2 * i ∧ (4 : ℤ) = 2 * j) := by
    refine' ⟨1, 2, by norm_num, by norm_num⟩
  have h₃ : ¬(∃ k : ℤ, (2 : ℤ) ^ 2 + (4 : ℤ) ^ 2 = 8 * k) := by
    rintro ⟨k, hk⟩
    norm_num at hk
    omega
  simp_all
