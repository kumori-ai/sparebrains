import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 15. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex15 {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  have h₃ : n / m ∣ n := Nat.div_dvd_of_dvd h₀
  have h₄ : n / m < n := by
    have h₄₁ : 1 < m := by omega
    have h₄₂ : 0 < n := by omega
    exact Nat.div_lt_self h₄₂ h₄₁
  exact ⟨h₃, h₄⟩
