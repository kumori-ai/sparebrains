import Mathlib

/-- Mathematics in Lean, Chapter 2 §1 (Calculating), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s01_ex03 (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  calc
  a * (b * c) = (a * b) * c := by rw [mul_assoc]
  _ = (b * a) * c := by rw [mul_comm a b]
  _ = b * (a * c) := by rw [mul_assoc]
  _ = b * (c * a) := by rw [mul_comm a c]
