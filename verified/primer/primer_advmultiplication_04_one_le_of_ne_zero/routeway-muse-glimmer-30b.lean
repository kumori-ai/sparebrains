import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 4: one_le_of_ne_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L04one_le_of_ne_zero.lean, Apache-2.0. -/
theorem primer_advmultiplication_04_one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  cases a with
  | zero => contradiction
  | succ n => exact Nat.succ_le_succ (Nat.zero_le n)
