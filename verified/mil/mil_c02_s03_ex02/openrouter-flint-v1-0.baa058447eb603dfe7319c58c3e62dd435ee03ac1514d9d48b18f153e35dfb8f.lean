import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex02 (a c d e : ℝ) (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  have h_exp : exp (a + d) ≤ exp (a + e) := by
    apply Real.exp_le_exp.mpr
    have h_add : a + d ≤ a + e := by
      calc
        a + d = d + a := by rw [add_comm]
        _ ≤ e + a := add_le_add_left h₀ a
        _ = a + e := by rw [add_comm]
    exact h_add
  exact add_le_add (le_refl c) h_exp
