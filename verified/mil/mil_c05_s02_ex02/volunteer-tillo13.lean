import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §2 (Induction and Recursion), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s02_ex02 (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  have key : ∀ m : ℕ, 6 * ∑ i ∈ range (m + 1), i ^ 2 = m * (m + 1) * (2 * m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, mul_add, ih]
      ring
  rw [← key n, Nat.mul_div_cancel_left _ (by norm_num)]
