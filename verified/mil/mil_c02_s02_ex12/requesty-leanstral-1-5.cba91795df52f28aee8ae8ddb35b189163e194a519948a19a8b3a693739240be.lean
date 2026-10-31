import Mathlib

/-- Mathematics in Lean, Chapter 2 §2 (Proving Identities in Algebraic Structures), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s02_ex12 {G : Type*} [Group G] (a : G) : a * a⁻¹ = 1 := by
  simpa using inv_mul_cancel_left a (b := 1)
