import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 1: mul_le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L01mul_le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_01_mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  exact Nat.mul_le_mul_right t h
