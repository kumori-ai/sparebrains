import Mathlib

open scoped Nat
open scoped Real

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  induction n, h₀ using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    simp only [Nat.add_sub_cancel]
    have hpow : n ^ (n - 1) < (n + 1) ^ (n - 1) := by
      apply pow_lt_pow_left₀ <;> omega
    have h1 : (n + 1) * n ! < (n + 1) * n ^ (n - 1) :=
      mul_lt_mul_of_pos_left ih (by omega)
    have h2 : (n + 1) * n ^ (n - 1) < (n + 1) * (n + 1) ^ (n - 1) :=
      mul_lt_mul_of_pos_left hpow (by omega)
    have h3 : (n + 1) * (n + 1) ^ (n - 1) = (n + 1) ^ n := by
      have h_eq : n - 1 + 1 = n := by omega
      calc (n + 1) * (n + 1) ^ (n - 1) = (n + 1) ^ (n - 1 + 1) := by rw [pow_succ']
        _ = (n + 1) ^ n := by rw [h_eq]
    calc (n + 1) ! = (n + 1) * n ! := Nat.factorial_succ n
      _ < (n + 1) * n ^ (n - 1) := h1
      _ < (n + 1) * (n + 1) ^ (n - 1) := h2
      _ = (n + 1) ^ n := h3
