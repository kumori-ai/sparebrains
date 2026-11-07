import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 15. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex15 {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  obtain ⟨k, hk⟩ := h₀
  have hm : 0 < m := by omega
  have hkpos : 0 < k := by
    by_contra h
    push_neg at h
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    simp at hk
    omega
  have hdiv : n / m = k := by
    rw [hk]
    exact Nat.mul_div_cancel_left k hm
  constructor
  · rw [hdiv]
    exact ⟨m, by rw [hk, mul_comm]⟩
  · rw [hdiv, hk]
    calc k = 1 * k := (one_mul k).symm
    _ < m * k := mul_lt_mul_of_pos_right (by omega) hkpos
