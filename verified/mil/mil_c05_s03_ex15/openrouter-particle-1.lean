import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 15. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex15 {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  rcases h₀ with ⟨k, rfl⟩
  have hmpos : 0 < m := by omega
  have hk : 1 < k := by
    have : m * 1 < m * k := by simpa using h₂
    exact (Nat.mul_lt_mul_left hmpos).mp this
  have hdiv : (m * k) / m = k := by
    exact Nat.mul_div_right k hmpos
  rw [hdiv]
  constructor
  · exact dvd_mul_left k m
  · have hm1 : 1 < m := by omega
    have hkpos : 0 < k := by omega
    have hlt : k * 1 < k * m := (Nat.mul_lt_mul_left hkpos).mpr hm1
    simpa [Nat.mul_comm] using hlt
