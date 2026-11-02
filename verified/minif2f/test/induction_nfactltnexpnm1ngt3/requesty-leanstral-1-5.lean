import Mathlib

open scoped Nat
open scoped Real

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  refine Nat.le_induction ?base ?step n h₀
  · norm_num
  · intro m hm h_ih
    have hm1 : 1 ≤ m := by omega
    have hm1_pos : 0 < m + 1 := by omega
    have h_pow_le : m ^ (m - 1) ≤ (m + 1) ^ (m - 1) :=
      Nat.pow_le_pow_left (Nat.le_succ m) (m - 1)
    have h_mul_le : (m + 1) * (m ^ (m - 1)) ≤ (m + 1) * ((m + 1) ^ (m - 1)) :=
      Nat.mul_le_mul_left (m + 1) h_pow_le
    have h_pow_succ : (m + 1) * ((m + 1) ^ (m - 1)) = (m + 1) ^ m := by
      calc
        (m + 1) * ((m + 1) ^ (m - 1)) = ((m + 1) ^ (m - 1)) * (m + 1) := by ring
        _ = (m + 1) ^ ((m - 1) + 1) := by rw [Nat.pow_succ]
        _ = (m + 1) ^ m := by rw [Nat.sub_add_cancel hm1]
    have h_mul_le' : (m + 1) * (m ^ (m - 1)) ≤ (m + 1) ^ m :=
      h_mul_le.trans h_pow_succ.le
    have h_fact_lt : (m + 1)! < (m + 1) * (m ^ (m - 1)) := by
      rw [Nat.factorial_succ]
      exact Nat.mul_lt_mul_of_pos_left h_ih hm1_pos
    exact lt_of_lt_of_le h_fact_lt h_mul_le'
