import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest integer greater than 10 that is both a perfect square and a perfect cube? -/
theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
  by_contra h
  have hn : n < 64 := by omega
  rcases h₁ with ⟨x, hx⟩
  rcases h₂ with ⟨t, ht⟩
  have hxlt : x < 8 := by
    by_contra hxge
    have hxge' : 8 ≤ x := by omega
    have hpow : 8 ^ 2 ≤ x ^ 2 := by gcongr
    norm_num at hpow
    have : 64 ≤ n := by
      rw [← hx]
      exact hpow
    omega
  have htlt : t < 4 := by
    by_contra htge
    have htge' : 4 ≤ t := by omega
    have hpow : 4 ^ 3 ≤ t ^ 3 := by gcongr
    norm_num at hpow
    have : 64 ≤ n := by
      rw [← ht]
      exact hpow
    omega
  interval_cases x <;> interval_cases t <;> norm_num at hx ht h₀ <;> omega
