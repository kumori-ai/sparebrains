import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex03 (a b : ℝ) (f : ℝ → ℝ) (h : Monotone f) (h' : f a < f b) : a < b := by
  by_contra hnot
  have hle : b ≤ a := (not_lt).mp hnot
  have hfb_le_fa : f b ≤ f a := h hle
  have hfa_le_fb : f a ≤ f b := le_of_lt h'
  have hEq : f a = f b := le_antisymm hfa_le_fb hfb_le_fa
  exact (ne_of_lt h') hEq
