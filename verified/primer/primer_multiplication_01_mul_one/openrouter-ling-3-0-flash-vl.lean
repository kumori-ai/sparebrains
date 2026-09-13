import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 1: mul_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L01mul_one.lean, Apache-2.0. -/
theorem primer_multiplication_01_mul_one (m : ℕ) : m * 1 = m := by
  exact mul_one m
