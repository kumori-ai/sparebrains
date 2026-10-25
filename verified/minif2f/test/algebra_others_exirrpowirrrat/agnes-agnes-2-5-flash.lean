import Mathlib

open scoped Nat
open scoped Real

theorem algebra_others_exirrpowirrrat : ∃ a b, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
  by_cases h : Irrational ((Real.sqrt 2) ^ Real.sqrt 2)
  · -- Case 1: √2^√2 is irrational
    use (Real.sqrt 2) ^ Real.sqrt 2, Real.sqrt 2
    constructor
    · exact h
    constructor
    · exact irrational_sqrt_two
    · -- Show ((√2)^√2)^√2 = 2, which is rational
      have : (((Real.sqrt 2) ^ Real.sqrt 2) ^ Real.sqrt 2 : ℝ) = 2 := by
        have : ((Real.sqrt 2) ^ Real.sqrt 2) > 0 := Real.rpow_pos_of_pos (by positivity) _
        calc
          (((Real.sqrt 2) ^ Real.sqrt 2) ^ Real.sqrt 2 : ℝ) 
            = (Real.sqrt 2) ^ (Real.sqrt 2 * Real.sqrt 2) := by
              rw [← Real.rpow_mul] <;> positivity
          _ = (Real.sqrt 2) ^ (2 : ℝ) := by
            simp [Real.sqrt_sq]
            <;> ring_nf
          _ = 2 := by
            have : (Real.sqrt 2) ^ (2 : ℝ) = 2 := by
              norm_num [Real.rpow_two]
            exact this
      rw [this]
      norm_num
  · -- Case 2: √2^√2 is rational
    use Real.sqrt 2, Real.sqrt 2
    constructor
    · exact irrational_sqrt_two
    constructor
    · exact irrational_sqrt_two
    · -- Show √2^√2 is rational (negation of irrational)
      exact h
