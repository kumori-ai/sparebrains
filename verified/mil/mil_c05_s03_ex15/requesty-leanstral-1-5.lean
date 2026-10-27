import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 15. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex15 {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  have hdiv : n / m ∣ n := by
    refine ⟨m, ?_⟩
    exact (Nat.div_mul_cancel h₀).symm
  have hlt : n / m < n := by
    have h₁' : 1 < m := by omega
    have h₂' : 1 ≤ n := by omega
    exact Nat.div_lt_self h₂' h₁'
  exact And.intro hdiv hlt
