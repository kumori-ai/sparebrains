import Mathlib

/-- Mathematics in Lean, Chapter 2 §1 (Calculating), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s01_ex03 (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  ring
