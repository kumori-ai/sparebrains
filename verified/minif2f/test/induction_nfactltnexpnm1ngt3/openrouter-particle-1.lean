import Mathlib

open scoped Nat
open scoped Real

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  refine Nat.le_induction ?base ?step n h₀
  · norm_num [Nat.factorial]
  · intro n hn ih
    calc
      (n + 1) ! = (n + 1) * n ! := by rw [Nat.factorial_succ]
      _ < (n + 1) * n ^ (n - 1) := by
        exact Nat.mul_lt_mul_of_pos_left ih (Nat.succ_pos n)
      _ ≤ (n + 1) * (n + 1) ^ (n - 1) := by
        gcongr
        exact Nat.le_succ n
      _ = (n + 1) ^ n := by
        have hn1 : 1 ≤ n := by omega
        calc
          (n + 1) * (n + 1) ^ (n - 1) = (n + 1) ^ ((n - 1) + 1) := by rw [pow_succ']
          _ = (n + 1) ^ n := by rw [Nat.sub_add_cancel hn1]
