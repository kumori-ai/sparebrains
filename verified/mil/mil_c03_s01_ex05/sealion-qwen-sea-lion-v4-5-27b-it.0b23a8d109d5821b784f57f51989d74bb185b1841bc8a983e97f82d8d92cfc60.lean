import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex05 (f : ℝ → ℝ) {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro x y hxy
  have hfy : f x ≤ f y := mf hxy
  exact mul_le_mul_of_nonneg_left hfy nnc
