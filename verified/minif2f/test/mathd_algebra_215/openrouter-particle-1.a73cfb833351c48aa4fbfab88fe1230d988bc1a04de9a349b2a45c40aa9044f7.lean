import Mathlib

open scoped Nat
open scoped Real

/-- What is the sum of the two values of $x$ for which $(x+3)^2 = 121$? -/
theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    ∑ k ∈ S, k = -6 := by
  classical
  have hS : S = ({8, -14} : Finset ℝ) := by
    ext x
    rw [h₀ x]
    constructor
    · intro hx
      have hzero : (x + 3 - 11) * (x + 3 + 11) = 0 := by
        nlinarith [hx]
      rcases mul_eq_zero.mp hzero with h1 | h2
      · have hx8 : x = 8 := by linarith
        simp [hx8]
      · have hxm14 : x = -14 := by linarith
        simp [hxm14]
    · intro hx
      simp at hx
      rcases hx with rfl | rfl <;> norm_num
  rw [hS]
  rw [Finset.sum_insert (by norm_num : (8 : ℝ) ∉ ({-14} : Finset ℝ))]
  rw [Finset.sum_singleton]
  norm_num
