import Mathlib

/-- Mathematics in Lean, Chapter 2 §2 (Proving Identities in Algebraic Structures), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s02_ex05 {R : Type*} [Ring R] {a b : R} (h : a + b = 0) : -a = b := by
  calc -a = -a + 0 := by simp [add_zero]
    _ = -a + (a + b) := by rw [h]
    _ = (-a + a) + b := by simp
    _ = 0 + b := by simp
    _ = b := by simp [zero_add]
