import Mathlib

/-- Mathematics in Lean, Chapter 2 §2 (Proving Identities in Algebraic Structures), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s02_ex02 {R : Type*} [Ring R] {a b c : R} (h : a + b = a + c) : b = c := by
  have h' : -a + (a + b) = -a + (a + c) := by
    rw [h]
  calc
    b = -a + (a + b) := by simp
    _ = -a + (a + c) := h'
    _ = c := by simp
