import Mathlib

/-- Mathematics in Lean, Chapter 2 §2 (Proving Identities in Algebraic Structures), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s02_ex02 {R : Type*} [Ring R] {a b c : R} (h : a + b = a + c) : b = c := by
  calc
  b = -a + (a + b) := by
    rw [← add_assoc, neg_add_cancel, zero_add]
  _ = -a + (a + c) := by
    rw [h]
  _ = c := by
    rw [← add_assoc, neg_add_cancel, zero_add]
