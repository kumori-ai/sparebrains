import Mathlib

open scoped Nat
open scoped Real

/-- Find the sum of all solutions of the equation $|2-x|= 3$. -/
theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    ∑ k ∈ S, k = 4 := by
  have hS : S = ({-1, 5} : Finset ℝ) := by
    ext x
    rw [h₀ x]
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 3)]
    constructor
    · intro h
      rcases h with h | h
      · have hx : x = -1 := by linarith
        simp [hx]
      · have hx : x = 5 := by linarith
        simp [hx]
    · intro h
      simp at h
      rcases h with h | h
      · subst x
        norm_num
      · subst x
        norm_num
  rw [hS]
  have h : (-1 : ℝ) ∉ ({5} : Finset ℝ) := by norm_num
  rw [Finset.sum_insert (f := fun x => x) h]
  rw [Finset.sum_singleton]
  norm_num
