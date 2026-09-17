import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 13. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex13 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  have h' : (m % 4 * (n % 4)) % 4 = 3 := by
    rw [Nat.mul_mod] at h
    exact h
  have hm : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  have hn : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  have hm_cases : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
    omega
  have hn_cases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    omega
  rcases hm_cases with (hm0 | hm1 | hm2 | hm3) <;>
    rcases hn_cases with (hn0 | hn1 | hn2 | hn3) <;>
      simp_all
