import Mathlib

open scoped Nat
open scoped Real

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  induction n, h₀ using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hpos : 0 < n + 1 := by omega
    have h1 : (n + 1) * n ! < (n + 1) * n ^ (n - 1) :=
      mul_lt_mul_of_pos_left ih hpos
    have h2 : n ^ (n - 1) ≤ (n + 1) ^ (n - 1) :=
      Nat.pow_le_pow_left (Nat.le_succ n) (n - 1)
    have h3 : (n + 1) * (n + 1) ^ (n - 1) = (n + 1) ^ n := by
      rw [← pow_succ']
      congr 1
      omega
    calc (n + 1) ! = (n + 1) * n ! := Nat.factorial_succ n
      _ < (n + 1) * n ^ (n - 1) := h1
      _ ≤ (n + 1) * (n + 1) ^ (n - 1) :=
        mul_le_mul_of_nonneg_left h2 (Nat.zero_le (n + 1))
      _ = (n + 1) ^ ((n + 1) - 1) := by
        rw [h3]
        simp
