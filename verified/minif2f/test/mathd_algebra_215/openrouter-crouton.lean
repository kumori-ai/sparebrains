import Mathlib

open scoped Nat
open scoped Real

/-- What is the sum of the two values of $x$ for which $(x+3)^2 = 121$? -/
theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    ∑ k ∈ S, k = -6 := by
  have hS : S = {-14, 8} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [h₀ x]
    constructor
    · intro h
      have h2 : (x + 3 - 11) * (x + 3 + 11) = 0 := by
        have heq : (x + 3 - 11) * (x + 3 + 11) = (x + 3) ^ 2 - 121 := by ring
        rw [heq, h]
        norm_num
      rcases mul_eq_zero.mp h2 with h3 | h3
      · right
        linarith
      · left
        linarith
    · intro h
      rcases h with rfl | rfl <;> norm_num
  rw [hS, Finset.sum_pair (by norm_num : (-14 : ℝ) ≠ 8)]
  norm_num
