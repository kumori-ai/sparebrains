import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 15. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex15 {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  have hmod : n % m = 0 := Nat.mod_eq_zero_of_dvd h₀
  have hdiv : n / m ∣ n := by
    refine ⟨m, ?_⟩
    have h := Nat.div_add_mod n m
    rw [hmod] at h
    simpa [mul_comm] using h.symm
  have hlt : n / m < n := by
    have hn : 0 < n := by omega
    have hm : 1 < m := by omega
    exact Nat.div_lt_self hn hm
  exact ⟨hdiv, hlt⟩
