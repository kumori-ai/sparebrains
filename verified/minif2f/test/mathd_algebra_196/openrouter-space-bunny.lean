import Mathlib

open scoped Nat
open scoped Real

/-- Find the sum of all solutions of the equation $|2-x|= 3$. -/
theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    ∑ k ∈ S, k = 4 := by
  have hS : S = {-1, 5} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      have hx' : abs (2 - x) = 3 := (h₀ x).mp hx
      by_cases h : 0 ≤ 2 - x
      · rw [abs_of_nonneg h] at hx'
        have hx'' : x = -1 := by linarith
        exact Or.inl hx''
      · have hneg : 2 - x ≤ 0 := le_of_not_ge h
        rw [abs_of_nonpos hneg] at hx'
        have hx'' : x = 5 := by linarith
        exact Or.inr hx''
    · intro hx
      rcases hx with hx | hx
      · subst x
        apply (h₀ (-1)).mpr
        norm_num
      · subst x
        apply (h₀ 5).mpr
        norm_num
  rw [hS]
  norm_num
