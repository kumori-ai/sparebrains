import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest integer greater than 10 that is both a perfect square and a perfect cube? -/
theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  have ht_ge : 3 ≤ t := by
    by_contra h
    push_neg at h
    interval_cases t <;> norm_num at ht <;> omega
  by_cases ht3 : t = 3
  · subst ht3
    norm_num at ht
    have hx_le : x ≤ 5 := by
      by_contra h
      push_neg at h
      have hle : (6 : ℕ) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left (by omega : (6 : ℕ) ≤ x) 2
      norm_num at hle
      omega
    have hle2 : x ^ 2 ≤ (5 : ℕ) ^ 2 := Nat.pow_le_pow_left hx_le 2
    norm_num at hle2
    omega
  · have ht_ge4 : 4 ≤ t := by omega
    have hle : (4 : ℕ) ^ 3 ≤ t ^ 3 := Nat.pow_le_pow_left ht_ge4 3
    norm_num at hle
    omega
