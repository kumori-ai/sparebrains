import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 15. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex15 {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  have hm : 0 < m := by omega
  have hn : 0 < n := lt_trans hm h₂
  constructor
  · refine ⟨m, (Nat.div_mul_cancel h₀).symm⟩
  · rw [Nat.div_lt_iff_lt_mul hm]
    have hnm : n < n * m := by
      simpa only [Nat.mul_one] using
        Nat.mul_lt_mul_of_pos_left (show 1 < m by omega) hn
    simpa only [Nat.mul_comm] using hnm
