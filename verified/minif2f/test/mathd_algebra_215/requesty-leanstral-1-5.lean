import Mathlib

open scoped Nat
open scoped Real

/-- What is the sum of the two values of $x$ for which $(x+3)^2 = 121$? -/
theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    ∑ k ∈ S, k = -6 := by
  have hS : S = {8, -14} := by
    ext x
    constructor
    · intro hx
      have h_eq : (x + 3) ^ 2 = 121 := (h₀ x).mp hx
      have h_factor : (x - 8) * (x + 14) = 0 := by
        nlinarith
      rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with (h | h)
      · have hx8 : x = 8 := by linarith
        simp [hx8]
      · have hx14 : x = -14 := by linarith
        simp [hx14]
    · intro hx
      simp at hx
      rcases hx with (rfl | rfl)
      · apply (h₀ 8).mpr; norm_num
      · apply (h₀ (-14)).mpr; norm_num
  rw [hS]
  norm_num
