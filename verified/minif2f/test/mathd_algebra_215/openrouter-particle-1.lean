import Mathlib

open scoped Nat
open scoped Real

/-- What is the sum of the two values of $x$ for which $(x+3)^2 = 121$? -/
theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    ∑ k ∈ S, k = -6 := by
  have hS : S = ({8, -14} : Finset ℝ) := by
    ext x
    rw [h₀ x]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have hfac : (x - 8) * (x + 14) = 0 := by
        nlinarith [h]
      rcases mul_eq_zero.mp hfac with hx | hx
      · left
        linarith
      · right
        linarith
    · intro hx
      rcases hx with rfl | rfl <;> norm_num
  rw [hS]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    norm_num
  · norm_num
