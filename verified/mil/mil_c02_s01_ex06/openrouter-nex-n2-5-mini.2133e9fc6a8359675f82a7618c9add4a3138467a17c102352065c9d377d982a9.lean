import Mathlib

/-- Mathematics in Lean, Chapter 2 §1 (Calculating), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s01_ex06 (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  calc
    c = b * a - d := by rw [hyp]
    _ = a * b - d := by rw [mul_comm]
    _ = d - d := by rw [hyp']
    _ = 0 := by ring
