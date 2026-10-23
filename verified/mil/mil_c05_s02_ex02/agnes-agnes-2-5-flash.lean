import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §2 (Induction and Recursion), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s02_ex02 (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    rw [ih]
    ring_nf
    <;> norm_num
    <;> ring_nf at *
    <;> omega
