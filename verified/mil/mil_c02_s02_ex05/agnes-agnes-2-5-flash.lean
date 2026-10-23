import Mathlib

/-- Mathematics in Lean, Chapter 2 §2 (Proving Identities in Algebraic Structures), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s02_ex05 {R : Type*} [Ring R] {a b : R} (h : a + b = 0) : -a = b := by
  have h1 : -a + (a + b) = -a + 0 := by rw [h]
  have h2 : (-a + a) + b = -a := by simpa using h1
  have h3 : 0 + b = -a := by simpa using h2
  have h4 : b = -a := by simpa using h3
  exact h4.symm
