import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have h₁ := h 2 4
  have h₂ : (∃ i j : ℤ, (2 : ℤ) = 2 * i ∧ (4 : ℤ) = 2 * j) := by
    refine' ⟨1, 2, by norm_num, by norm_num⟩
  have h₃ : (∃ k : ℤ, (2 : ℤ) ^ 2 + (4 : ℤ) ^ 2 = 8 * k) := by
    exact h₁.mp h₂
  have h₄ : ¬(∃ k : ℤ, (2 : ℤ) ^ 2 + (4 : ℤ) ^ 2 = 8 * k) := by
    rintro ⟨k, hk⟩
    have h₅ : (8 : ℤ) * k = 20 := by
      norm_num at hk ⊢
      linarith
    have h₆ : (8 : ℤ) ∣ 20 := by
      use k
      linarith
    have h₇ : (20 : ℤ) % 8 = 0 := Int.dvd_iff_emod_eq_zero.mp h₆
    norm_num at h₇
  exact h₄ h₃
