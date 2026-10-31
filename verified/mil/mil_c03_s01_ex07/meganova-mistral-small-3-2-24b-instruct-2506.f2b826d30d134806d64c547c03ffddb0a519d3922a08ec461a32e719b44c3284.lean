import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex07 (f g : ℝ → ℝ) (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  have hf : ∀ x y, x ≤ y → f x ≤ f y := mf
  have hg : ∀ x y, x ≤ y → g x ≤ g y := mg
  intro x y hxy
  apply hf (g x) (g y)
  exact hg x y hxy
