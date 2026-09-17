import Mathlib

open scoped Nat
open scoped Real

/-- What is the sum of the two values of $x$ for which $(x+3)^2 = 121$? -/
theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    ∑ k ∈ S, k = -6 := by
  have hS : S = ({8, -14} : Finset ℝ) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
    constructor
    · intro hx
      have hx' : (x + 3) ^ 2 = (11 : ℝ) ^ 2 := by
        rw [hx]
        norm_num
      have hx'' : (x - 8) * (x + 14) = 0 := by
        have : (x + 3) ^ 2 - (11 : ℝ) ^ 2 = 0 := by linarith
        ring_nf at this ⊢
        exact this
      have hx''' : x - 8 = 0 ∨ x + 14 = 0 := by
        exact eq_zero_or_eq_zero_of_mul_eq_zero hx''
      cases hx''' with
      | inl h => exact Or.inl (sub_eq_zero.mp h)
      | inr h => exact Or.inr (by linarith)
    · rintro (rfl | rfl) <;> norm_num
  rw [hS]
  rw [Finset.sum_pair (by norm_num : (8 : ℝ) ≠ -14)]
  norm_num
