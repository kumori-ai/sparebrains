import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex04 (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have ha_pos : 0 < 1 + exp a := by
    linarith [Real.exp_pos a]
  have h_exp : exp a ≤ exp b := Real.exp_le_exp.mpr h
  have h_sum : 1 + exp a ≤ 1 + exp b := by linarith
  exact Real.log_le_log ha_pos h_sum
