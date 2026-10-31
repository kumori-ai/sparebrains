import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 13. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex13 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  have hm4_lt : m % 4 < 4 := Nat.mod_lt m (by norm_num : 0 < 4)
  have hn4_lt : n % 4 < 4 := Nat.mod_lt n (by norm_num : 0 < 4)
  have hm4_cases : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  have hn4_cases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have hmod : ((m % 4) * (n % 4)) % 4 = 3 := by
    calc
      ((m % 4) * (n % 4)) % 4 = (m * n) % 4 := by rw [← Nat.mul_mod]
      _ = 3 := h
  rcases hm4_cases with (hm | hm | hm | hm)
  · rw [hm] at hmod; norm_num at hmod
  · rw [hm] at hmod; simp at hmod; right; exact hmod
  · rw [hm] at hmod
    rcases hn4_cases with (hn | hn | hn | hn)
    · rw [hn] at hmod; norm_num at hmod
    · rw [hn] at hmod; norm_num at hmod
    · rw [hn] at hmod; norm_num at hmod
    · rw [hn] at hmod; norm_num at hmod
  · left; exact hm
