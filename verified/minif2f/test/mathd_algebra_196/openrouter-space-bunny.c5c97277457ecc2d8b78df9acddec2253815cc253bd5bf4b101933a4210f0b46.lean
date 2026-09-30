import Mathlib

open scoped Nat
open scoped Real

/-- Find the sum of all solutions of the equation $|2-x|= 3$. -/
theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    ∑ k ∈ S, k = 4 := by
  have hS : S = ({-1, 5} : Finset ℝ) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      have hx' := (h₀ x).mp hx
      by_cases hnonneg : 0 ≤ 2 - x
      · left
        rw [abs_of_nonneg hnonneg] at hx'
        linarith
      · right
        have hnonpos : 2 - x ≤ 0 := le_of_not_ge hnonneg
        rw [abs_of_nonpos hnonpos] at hx'
        linarith
    · rintro (rfl | rfl)
      · apply (h₀ (-1)).mpr
        norm_num [abs_of_nonneg (show (0 : ℝ) ≤ 2 - -1 by norm_num)]
      · apply (h₀ 5).mpr
        norm_num [abs_of_nonpos (show (2 : ℝ) - 5 ≤ 0 by norm_num)]
  rw [hS]
  norm_num
