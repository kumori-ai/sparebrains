import Mathlib

open Function

/-- Mathematics in Lean, Chapter 3 §2 (The Existential Quantifier), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s02_ex06 {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro b
  refine ⟨b * c⁻¹, ?_⟩
  show c * (b * c⁻¹) = b
  calc c * (b * c⁻¹) = b * (c * c⁻¹) := by ring
    _ = b * 1 := by rw [mul_inv_cancel₀ h]
    _ = b := mul_one b
