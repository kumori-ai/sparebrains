import Mathlib

/-- Mathematics in Lean, Chapter 2 §1 (Calculating), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s01_ex05 (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c, h, ← mul_assoc a e f]
