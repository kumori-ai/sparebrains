import Mathlib

open scoped Nat
open scoped Real

theorem algebra_others_exirrpowirrrat : ∃ a b, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
  by_cases h : Irrational (Real.sqrt 2 ^ Real.sqrt 2)
  · refine ⟨Real.sqrt 2 ^ Real.sqrt 2, Real.sqrt 2, h, irrational_sqrt_two, ?_⟩
    have hpow : (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2 = 2 := by
      rw [← Real.rpow_mul (Real.sqrt_nonneg 2)]
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
      rw [Real.rpow_natCast]
      exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [hpow]
    intro h2
    exact h2 ⟨(2 : ℚ), by norm_num⟩
  · exact ⟨Real.sqrt 2, Real.sqrt 2, irrational_sqrt_two, irrational_sqrt_two, h⟩
