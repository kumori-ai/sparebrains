import Mathlib

open scoped Nat
open scoped Real

/-- What is the sum of the two values of $x$ for which $(x+3)^2 = 121$? -/
theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    ∑ k ∈ S, k = -6 := by
  have h₁ : S = {-14, 8} := by
    apply Finset.ext
    intro x
    simp [h₀]
    constructor
    · intro h
      have h₂ : (x + 3 - 11) * (x + 3 + 11) = 0 := by
        have h₃ : (x + 3) ^ 2 = 121 := h
        nlinarith
      have h₄ : x + 3 - 11 = 0 ∨ x + 3 + 11 = 0 := by
        apply eq_zero_or_eq_zero_of_mul_eq_zero h₂
      cases h₄ with
      | inl h₄ =>
        have h₅ : x = 8 := by linarith
        simp [h₅]
      | inr h₄ =>
        have h₅ : x = -14 := by linarith
        simp [h₅]
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
