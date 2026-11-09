import Mathlib

open scoped Nat
open scoped Real

theorem algebra_others_exirrpowirrrat : ∃ a b, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
  by_cases h : ∃ r : ℚ, (r : ℝ) = ((Real.sqrt 2) ^ (Real.sqrt 2))
  · refine ⟨Real.sqrt 2, Real.sqrt 2, irrational_sqrt_two, irrational_sqrt_two, ?_⟩
    intro hirr
    exact hirr h
  · have hirr : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2)) := h
    refine ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, hirr, irrational_sqrt_two, ?_⟩
    have hpos : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg _
    have h_eq : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = (2 : ℝ) := by
      calc
        ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = (Real.sqrt 2) ^ ((Real.sqrt 2) * (Real.sqrt 2)) := by
          rw [← Real.rpow_mul hpos (Real.sqrt 2) (Real.sqrt 2)]
        _ = (Real.sqrt 2) ^ (2 : ℝ) := by
          rw [Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        _ = (Real.sqrt 2) ^ 2 := by rw [Real.rpow_two]
        _ = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h_rational : ∃ r : ℚ, (r : ℝ) = ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) := by
      rw [h_eq]
      refine ⟨(2 : ℚ), by norm_num⟩
    intro hirr'
    exact hirr' h_rational
