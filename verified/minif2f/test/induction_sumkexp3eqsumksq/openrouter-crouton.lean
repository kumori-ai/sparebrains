import Mathlib

open scoped Nat
open scoped Real

theorem induction_sumkexp3eqsumksq (n : ℕ) :
    ∑ k ∈ Finset.range n, k ^ 3 = (∑ k ∈ Finset.range n, k) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    cases n with
    | zero => simp
    | succ m =>
      have h := Finset.sum_range_id_mul_two (m + 1)
      simp at h
      have h2 : (∑ k ∈ Finset.range (m + 1), k) * 2 * (m + 1) + (m + 1) ^ 2 = (m + 1) ^ 3 := by
        have h3 : (∑ k ∈ Finset.range (m + 1), k) * 2 * (m + 1) = (m + 1) * m * (m + 1) := by
          rw [h]
        rw [h3]
        ring
      rw [← h2]
      ring
