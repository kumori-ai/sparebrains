import Mathlib

open Function

/-- Mathematics in Lean, Chapter 3 §2 (The Existential Quantifier), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s02_ex06 {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro y
  refine ⟨c⁻¹ * y, ?_⟩
  show c * (c⁻¹ * y) = y
  rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]
