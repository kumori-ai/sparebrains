import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 15. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex15 {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  have hpos : 0 < n := by
    linarith
  have hm_gt_one : 1 < m := by
    linarith
  have h_lt : n / m < n :=
    Nat.div_lt_self hpos hm_gt_one
  have h_dvd : n / m ∣ n := by
    exact ⟨m, (Nat.div_mul_cancel h₀).symm⟩
  exact And.intro h_dvd h_lt
