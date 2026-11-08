import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex04 (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have hpos : (0 : ℝ) < 1 + exp a := by
    have h1 := exp_pos a
    linarith
  have hle : 1 + exp a ≤ 1 + exp b := by
    have h2 := exp_le_exp.mpr h
    linarith
  exact log_le_log hpos hle
