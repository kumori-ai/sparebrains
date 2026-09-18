import Mathlib

open BigOperators

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex01 {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m with
  | zero =>
    exfalso
    exact h0 rfl
  | succ m =>
    cases m with
    | zero =>
      exfalso
      exact h1 rfl
    | succ k =>
      exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
