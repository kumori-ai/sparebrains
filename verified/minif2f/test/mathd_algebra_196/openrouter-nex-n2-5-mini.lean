import Mathlib

open scoped Nat
open scoped Real

/-- Find the sum of all solutions of the equation $|2-x|= 3$. -/
theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    ∑ k ∈ S, k = 4 := by
  have h₂ (x : ℝ) : abs (2 - x) = 3 ↔ x = -1 ∨ x = 5 := by
    constructor
    · intro h
      by_cases h₃ : 2 - x ≥ 0
      · have h₄ : abs (2 - x) = 2 - x := abs_of_nonneg h₃
        have h₅ : 2 - x = 3 := by
          rw [h₄] at h
          exact h
        have h₆ : x = -1 := by linarith
        exact Or.inl h₆
      · have h₄ : 2 - x < 0 := lt_of_not_ge h₃
        have h₅ : abs (2 - x) = -(2 - x) := abs_of_neg h₄
        have h₆ : -(2 - x) = 3 := by
          rw [h₅] at h
          exact h
        have h₇ : x = 5 := by linarith
        exact Or.inr h₇
    · rintro (rfl | rfl) <;> norm_num [abs]
  have h₁ : S = {-1, 5} := by
    ext x
    simp [h₀, h₂]
  rw [h₁]
  norm_num
