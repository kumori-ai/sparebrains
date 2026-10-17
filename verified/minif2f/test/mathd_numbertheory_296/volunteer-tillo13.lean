import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest positive integer, other than $1$, that is both a perfect cube and a perfect fourth power? -/
theorem mathd_numbertheory_296 : IsLeast {n : ℕ | 2 ≤ n ∧ ∃ x, x ^ 3 = n ∧ ∃ t, t ^ 4 = n} 4096 := by
  constructor
  · exact ⟨by norm_num, 16, by norm_num, 8, by norm_num⟩
  · rintro n ⟨hn, x, hx, t, ht⟩
    by_contra h
    push_neg at h
    have ht8 : t < 8 := by
      by_contra h'
      push_neg at h'
      have : 8 ^ 4 ≤ t ^ 4 := Nat.pow_le_pow_left h' 4
      omega
    have hx16 : x < 16 := by
      by_contra h'
      push_neg at h'
      have : 16 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left h' 3
      omega
    subst hx
    interval_cases t <;> interval_cases x <;> omega
