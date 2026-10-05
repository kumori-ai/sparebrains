import Mathlib

/-- Mathematics in Lean, Chapter 2 §1 (Calculating), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s01_ex01 (a b c : ℝ) : c * b * a = b * (a * c) := by
  ring
