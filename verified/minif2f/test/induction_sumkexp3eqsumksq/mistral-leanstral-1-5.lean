import Mathlib

open scoped Nat
open scoped Real

theorem induction_sumkexp3eqsumksq (n : ℕ) :
    ∑ k ∈ Finset.range n, k ^ 3 = (∑ k ∈ Finset.range n, k) ^ 2 := by
  have two_mul_sum_range_eq (n : ℕ) : 2 * (∑ k ∈ Finset.range n, k) = n * (n-1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      cases n with
      | zero => simp
      | succ n =>
        simp [Nat.succ_sub_succ, Nat.sub_zero]
        ring
  have cube_eq_sq_mul_pred_add_sq (n : ℕ) : n^3 = n^2 * (n-1) + n^2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp [Nat.succ_sub_succ, Nat.sub_zero]
      ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [ih]
    have h := two_mul_sum_range_eq n
    have h2 : n^3 = n^2 * (n-1) + n^2 := cube_eq_sq_mul_pred_add_sq n
    have h' : n^2 * (n-1) = 2 * (∑ k ∈ Finset.range n, k) * n := by
      calc
        n^2 * (n-1) = n * (n * (n-1)) := by ring
        _ = n * (2 * (∑ k ∈ Finset.range n, k)) := by rw [← h]
        _ = 2 * (∑ k ∈ Finset.range n, k) * n := by ring
    calc
      (∑ k ∈ Finset.range n, k) ^ 2 + n ^ 3 = (∑ k ∈ Finset.range n, k) ^ 2 + (n^2 * (n-1) + n^2) := by rw [h2]
      _ = ((∑ k ∈ Finset.range n, k) ^ 2 + n^2 * (n-1)) + n^2 := by ring
      _ = ((∑ k ∈ Finset.range n, k) ^ 2 + 2 * (∑ k ∈ Finset.range n, k) * n) + n^2 := by rw [h']
      _ = ((∑ k ∈ Finset.range n, k) + n)^2 := by ring
