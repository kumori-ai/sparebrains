import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest integer greater than 10 that is both a perfect square and a perfect cube? -/
theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
  rcases h₁ with ⟨x, hx⟩
  rcases h₂ with ⟨t, ht⟩
  by_contra! h
  -- h : n < 64
  have hx_lt_8 : x < 8 := by
    by_contra! hx'
    have hx8 : 8 ≤ x := by omega
    have hsq : 64 ≤ x ^ 2 := by
      calc
        64 = 8 ^ 2 := by norm_num
        _ ≤ x ^ 2 := Nat.pow_le_pow_left hx8 2
    omega
  have ht_lt_4 : t < 4 := by
    by_contra! ht'
    have ht4 : 4 ≤ t := by omega
    have hcu : 64 ≤ t ^ 3 := by
      calc
        64 = 4 ^ 3 := by norm_num
        _ ≤ t ^ 3 := Nat.pow_le_pow_left ht4 3
    omega
  have h_all : ∀ n : ℕ, 10 ≤ n → n < 64 → ¬ ((∃ x ∈ Finset.range 8, x ^ 2 = n) ∧ (∃ t ∈ Finset.range 4, t ^ 3 = n)) := by
    decide
  have h_sq : ∃ x ∈ Finset.range 8, x ^ 2 = n := by
    refine ⟨x, Finset.mem_range.mpr hx_lt_8, hx⟩
  have h_cu : ∃ t ∈ Finset.range 4, t ^ 3 = n := by
    refine ⟨t, Finset.mem_range.mpr ht_lt_4, ht⟩
  exact h_all n h₀ h ⟨h_sq, h_cu⟩
