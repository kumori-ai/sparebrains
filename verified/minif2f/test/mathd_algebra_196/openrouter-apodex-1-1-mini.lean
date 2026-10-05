import Mathlib

open scoped Nat
open scoped Real

/-- Find the sum of all solutions of the equation $|2-x|= 3$. -/
theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    ∑ k ∈ S, k = 4 := by
  have h₁ : S = { -1, 5 } := by
    apply Finset.ext
    intro x
    simp [h₀]
    constructor
    · intro h
      by_cases h₂ : 2 - x ≥ 0
      · have h₃ : 2 - x = 3 := by
          rw [abs_of_nonneg h₂] at h
          exact h
        have : x = -1 := by linarith
        left; exact this
      · have h₃ : -(2 - x) = 3 := by
          rw [abs_of_nonpos (by linarith)] at h
          exact h
        have : x = 5 := by linarith
        right; exact this
    · intro h
      cases' h with h h
      · rw [h]; norm_num
      · rw [h]; norm_num
  rw [h₁]
  norm_num
