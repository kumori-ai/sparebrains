import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex04 (a b : ℝ) (f : ℝ → ℝ) (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro hm
  have hle : f a ≤ f b := hm h
  linarith
