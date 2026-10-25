import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 4: one_le_of_ne_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L04one_le_of_ne_zero.lean, Apache-2.0. -/
theorem primer_advmultiplication_04_one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  have hpos : 0 < a := Nat.pos_of_ne_zero ha
  exact Nat.succ_le_of_lt hpos
