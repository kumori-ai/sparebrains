import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 6: two_mul. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L06two_mul.lean, Apache-2.0. -/
theorem primer_multiplication_06_two_mul (m : ℕ) : 2 * m = m + m := by
  exact Nat.two_mul m
