import Mathlib

open Function

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 16. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex16 {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x y hxy
  rw [mul_eq_mul_left_iff] at hxy
  cases hxy with
  | inl hxy => exact hxy
  | inr hxy => exact (h hxy).elim
