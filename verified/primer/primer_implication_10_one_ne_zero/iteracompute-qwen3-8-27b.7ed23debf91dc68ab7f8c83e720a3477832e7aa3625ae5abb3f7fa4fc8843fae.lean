import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 10: 1 ≠ 0. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L10one_ne_zero.lean, Apache-2.0. -/
theorem primer_implication_10_one_ne_zero : (1 : ℕ) ≠ 0 := by
  exact Nat.succ_ne_zero 0
