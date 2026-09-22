import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex05 (a b c : ℝ) (h : a ≤ b) : c - exp b ≤ c - exp a := by
  have h1 : exp a ≤ exp b := by
    apply Real.exp_le_exp_of_le
    exact h
  have h2 : -exp b ≤ -exp a := by
    apply neg_le_neg
    exact h1
  have h3 : c - exp b ≤ c - exp a := by
    linarith [h2]
  exact h3
