import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex04 (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  apply log_le_log
  · positivity
  · have h_exp : exp a ≤ exp b := exp_le_exp.2 h
    exact add_le_add_right h_exp 1
