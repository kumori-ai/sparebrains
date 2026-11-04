import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 5: one_mul. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L05one_mul.lean, Apache-2.0. -/
theorem primer_multiplication_05_one_mul (m : ℕ) : 1 * m = m := by
  exact one_mul m
