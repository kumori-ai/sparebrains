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
      have h₂ : abs (2 - x) = 3 := by simpa using h
      have h₃ : 2 - x = 3 ∨ 2 - x = -3 := by
        rw [abs_eq (show (0 : ℝ) ≤ 3 by norm_num)] at h₂
        <;> tauto
      cases h₃ with
      | inl h₃ =>
        have : x = -1 := by linarith
        rw [this]
        norm_num
      | inr h₃ =>
        have : x = 5 := by linarith
        rw [this]
        norm_num
    · intro h
      have h₂ : x = -1 ∨ x = 5 := by tauto
      cases h₂ with
      | inl h₂ =>
        rw [h₂]
        norm_num
      | inr h₂ =>
        rw [h₂]
        norm_num
  rw [h₁]
  norm_num
