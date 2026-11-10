import Mathlib

open scoped Nat
open scoped Real

/-- Find the sum of all solutions of the equation $|2-x|= 3$. -/
theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    ∑ k ∈ S, k = 4 := by
  have h₁ : S = {-1, 5} := by
    apply Finset.ext
    intro x
    simp [h₀]
    constructor
    · intro h
      have h₂ : 2 - x = 3 ∨ 2 - x = -3 := by
        rw [abs_eq (show (0 : ℝ) ≤ 3 by norm_num)] at h
        exact h
      cases h₂ with
      | inl h₂ =>
        have h₃ : x = -1 := by linarith
        exact Or.inl h₃
      | inr h₂ =>
        have h₃ : x = 5 := by linarith
        exact Or.inr h₃
    · intro h
      cases h with
      | inl h =>
        rw [h]
        norm_num
      | inr h =>
        rw [h]
        norm_num
  rw [h₁]
  norm_num
