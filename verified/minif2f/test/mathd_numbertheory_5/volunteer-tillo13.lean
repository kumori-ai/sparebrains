import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest integer greater than 10 that is both a perfect square and a perfect cube? -/
theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
  obtain ⟨x, rfl⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  by_contra hlt
  push_neg at hlt
  have hx : x < 8 := by nlinarith
  have htt : t < 4 := by
    by_contra h4
    push_neg at h4
    have h64 : 4 ^ 3 ≤ t ^ 3 := Nat.pow_le_pow_left h4 3
    norm_num at h64
    linarith
  interval_cases x <;> interval_cases t <;> simp_all
