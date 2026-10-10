import Mathlib

open scoped Nat
open scoped Real

/-- Find the sum of all solutions of the equation $|2-x|= 3$. -/
theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    ∑ k ∈ S, k = 4 := by
  have h₁ : S = {-1, 5} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
    constructor
    · intro h
      by_cases h₂ : 2 - x ≥ 0
      · have h₃ : |2 - x| = 2 - x := by rw [abs_of_nonneg h₂]
        rw [h₃] at h
        have : x = -1 := by linarith
        simp [this]
      · have h₃ : |2 - x| = -(2 - x) := by rw [abs_of_nonpos (by linarith)]
        rw [h₃] at h
        have : x = 5 := by linarith
        simp [this]
    · intro h
      cases' h with h h
      · rw [h]; norm_num [abs_of_nonneg]
      · rw [h]; norm_num [abs_of_nonpos]
  rw [h₁]
  norm_num
