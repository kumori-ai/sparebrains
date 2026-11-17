import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 13. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex13 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  let a := m % 4
  let b := n % 4
  have ha : a < 4 := by
    dsimp [a]
    exact Nat.mod_lt _ (by norm_num)
  have hb : b < 4 := by
    dsimp [b]
    exact Nat.mod_lt _ (by norm_num)
  have hh : a * b % 4 = 3 := by
    have h' := h
    rw [Nat.mul_mod] at h'
    simpa [a, b] using h'
  change a = 3 ∨ b = 3
  interval_cases a <;> interval_cases b <;> simp_all
