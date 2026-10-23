import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex02 (a c d e : ℝ) (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  have h₁ : a + d ≤ a + e := by linarith
  have h₂ : exp (a + d) ≤ exp (a + e) := exp_le_exp.mpr h₁
  linarith
