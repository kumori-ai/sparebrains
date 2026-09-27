import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 9: mul_left_cancel. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L09mul_left_cancel.lean, Apache-2.0. -/
theorem primer_advmultiplication_09_mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero ha) h
