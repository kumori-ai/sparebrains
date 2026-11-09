import Mathlib

open scoped Nat
open scoped Real

theorem induction_sumkexp3eqsumksq (n : ℕ) :
    ∑ k ∈ Finset.range n, k ^ 3 = (∑ k ∈ Finset.range n, k) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h := Finset.sum_range_id_mul_two n
    cases n with
    | zero => simp
    | succ m =>
      have h' : (∑ i ∈ Finset.range (m + 1), i) * 2 = (m + 1) * m := by
        simpa using h
      have h2 : (∑ k ∈ Finset.range (m + 1), k) * 2 * (m + 1)
          = (m + 1) * m * (m + 1) := by
        rw [h']
      calc (∑ k ∈ Finset.range (m + 1), k) ^ 2 + (m + 1) ^ 3
          = (∑ k ∈ Finset.range (m + 1), k) ^ 2
            + (2 * (∑ k ∈ Finset.range (m + 1), k) * (m + 1) + (m + 1) ^ 2) := by
            congr 1
            calc (m + 1) ^ 3 = (m + 1) * m * (m + 1) + (m + 1) ^ 2 := by ring
            _ = (∑ k ∈ Finset.range (m + 1), k) * 2 * (m + 1) + (m + 1) ^ 2 := by
                  rw [← h2]
            _ = 2 * (∑ k ∈ Finset.range (m + 1), k) * (m + 1) + (m + 1) ^ 2 := by ring
        _ = ((∑ k ∈ Finset.range (m + 1), k) + (m + 1)) ^ 2 := by ring
