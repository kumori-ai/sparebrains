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
    interval_cases t <;> simp at ht <;> omega
  have hn27 : 27 ≤ n := by
    have h : (3 : ℕ) ^ 3 ≤ t ^ 3 := Nat.pow_le_pow_left ht_ge 3
    norm_num at h
    rw [ht] at h
    exact h
  have hx_ge : 6 ≤ x := by
    by_contra h
    push_neg at h
    interval_cases x <;> simp at hx <;> omega
  have hn36 : 36 ≤ n := by
    have h : (6 : ℕ) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hx_ge 2
    norm_num at h
    rw [hx] at h
    exact h
  have ht_ge4 : 4 ≤ t := by
    by_contra h
    push_neg at h
    interval_cases t <;> simp at ht <;> omega
  have h : (4 : ℕ) ^ 3 ≤ t ^ 3 := Nat.pow_le_pow_left ht_ge4 3
  norm_num at h
  rw [ht] at h
  exact h
