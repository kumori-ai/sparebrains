import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex05 (a b c : ℝ) (h : a ≤ b) : c - exp b ≤ c - exp a := by
  have h_exp : exp a ≤ exp b := exp_le_exp.mpr h
  have h_neg : -exp b ≤ -exp a := neg_le_neg h_exp
  exact add_le_add_right h_neg c
