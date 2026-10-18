import Mathlib

open scoped Nat
open scoped Real

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  refine Nat.le_induction ?base ?step n h₀
  · -- base case n = 3
    norm_num
  · -- inductive step
    intro m hm h_ih
    have hm1 : 1 ≤ m := by omega
    have hm1_ne_zero : m - 1 ≠ 0 := by omega
    calc
      (m + 1)! = (m + 1) * m ! := by rw [Nat.factorial_succ]
      _ < (m + 1) * (m ^ (m - 1)) :=
        Nat.mul_lt_mul_of_pos_left h_ih (Nat.succ_pos m)
      _ < (m + 1) * ((m + 1) ^ (m - 1)) :=
        Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left (by omega) hm1_ne_zero) (Nat.succ_pos m)
      _ = ((m + 1) ^ (m - 1)) * (m + 1) := by rw [mul_comm]
      _ = (m + 1) ^ ((m - 1) + 1) := by rw [Nat.pow_succ]
      _ = (m + 1) ^ m := by rw [Nat.sub_add_cancel hm1]
