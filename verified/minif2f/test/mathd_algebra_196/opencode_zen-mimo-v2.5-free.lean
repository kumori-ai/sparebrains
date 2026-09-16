import Mathlib

open scoped Nat
open scoped Real

/-- Find the sum of all solutions of the equation $|2-x|= 3$. -/
theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    ∑ k ∈ S, k = 4 := by
  have h₁ : ∀ x : ℝ, abs (2 - x) = 3 ↔ x = -1 ∨ x = 5 := by
    intro x
    constructor
    · intro h
      rw [abs_eq (by norm_num : (0:ℝ) ≤ 3)] at h
      cases h with
      | inl h => left; linarith
      | inr h => right; linarith
    · intro h
      cases h with
      | inl h => subst h; norm_num
      | inr h => subst h; norm_num
  have h₂ : ∀ x : ℝ, x ∈ S ↔ x = -1 ∨ x = 5 := by
    intro x
    rw [h₀, h₁]
  have hS : S = {-1, 5} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact h₂ x
  have hne : (-1:ℝ) ≠ 5 := by norm_num
  rw [hS, Finset.sum_pair hne]
  norm_num
