import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 15. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex15 {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  obtain ⟨k, rfl⟩ := h₀
  have hm : 0 < m := by omega
  have hdiv : m * k / m = k := Nat.mul_div_cancel_left k hm
  rw [hdiv]
  constructor
  · exact dvd_mul_left k m
  · cases k with
    | zero => simp at h₂
    | succ k' =>
      have hlt : 1 * (k' + 1) < m * (k' + 1) :=
        mul_lt_mul_of_pos_right h₁ (Nat.succ_pos k')
      simpa using hlt
