import Mathlib

/-- Mathematics in Lean, Chapter 2 §2 (Proving Identities in Algebraic Structures), exercise 10. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s02_ex10 {R : Type*} [Ring R] : 1 + 1 = (2 : R) := by
  norm_num
