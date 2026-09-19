import Mathlib

open scoped Nat
open scoped Real

theorem algebra_others_exirrpowirrrat : ∃ a b, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
  by_cases h : Irrational (Real.sqrt 2 ^ Real.sqrt 2)
  · have hpow : (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2 = 2 := by
      calc
        (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2
            = Real.sqrt 2 ^ (Real.sqrt 2 * Real.sqrt 2) := by
          rw [Real.rpow_mul (Real.sqrt_nonneg 2)]
        _ = Real.sqrt 2 ^ (2 : ℝ) := by
          rw [show Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) by
            nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]]
        _ = 2 := by
          rw [Real.rpow_two]
          exact Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    exact ⟨Real.sqrt 2 ^ Real.sqrt 2, Real.sqrt 2, h, irrational_sqrt_two, by
      rw [hpow]
      exact fun h2 : Irrational (2 : ℝ) => h2 ⟨2, by norm_num⟩⟩
  · exact ⟨Real.sqrt 2, Real.sqrt 2, irrational_sqrt_two, irrational_sqrt_two, h⟩
