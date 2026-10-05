import Mathlib

/-- Mathematics in Lean, Chapter 2 §2 (Proving Identities in Algebraic Structures), exercise 9. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s02_ex09 {R : Type*} [Ring R] (a : R) : a - a = 0 := by
  rw [sub_self]
