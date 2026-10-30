import Mathlib

open scoped Nat
open scoped Real

/-- Find the sum of all solutions of the equation $|2-x|= 3$. -/
theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    ∑ k ∈ S, k = 4 := by
  have hS : S = {-1, 5} := by
    ext x
    constructor
    · intro hx
      rcases h₀ x |>.mp hx with h
      have h' : 2 - x = 3 ∨ 2 - x = -3 := by
        rw [abs_eq (by norm_num : 0 ≤ (3 : ℝ))] at h
        exact h
      rcases h' with h1 | h2
      · have : x = -1 := by linarith
        subst this
        simp
      · have : x = 5 := by linarith
        subst this
        simp
    · intro hx
      simp at hx
      rcases hx with (hx | hx)
      · subst hx
        apply (h₀ (-1)).mpr
        norm_num
      · subst hx
        apply (h₀ (5 : ℝ)).mpr
        norm_num
  rw [hS]
  norm_num
