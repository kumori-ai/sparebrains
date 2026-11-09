import Mathlib

open scoped Nat
open scoped Real

/-- Find the sum of all solutions of the equation $|2-x|= 3$. -/
theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    ∑ k ∈ S, k = 4 := by
  have hS : S = {-1, 5} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [h₀ x]
    constructor
    · intro h
      rcases eq_or_eq_neg_of_abs_eq h with h1 | h1
      · left
        linarith
      · right
        linarith
    · intro h
      rcases h with rfl | rfl <;> norm_num
  rw [hS, Finset.sum_pair (by norm_num)]
  norm_num
