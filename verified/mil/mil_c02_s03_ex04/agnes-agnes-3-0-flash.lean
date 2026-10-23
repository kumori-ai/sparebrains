import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex04 (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h1 : 0 < 1 + exp a := by
    positivity
  have h2 : 0 < 1 + exp b := by
    positivity
  have h3 : exp a ≤ exp b := by
    exact Real.exp_le_exp.mpr h
  have h4 : 1 + exp a ≤ 1 + exp b := by
    linarith
  have h5 : log (1 + exp a) ≤ log (1 + exp b) := by
    exact Real.log_le_log h1 h4
  exact h5
