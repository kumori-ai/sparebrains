import Mathlib

/-- Natural Number Game (Lean 4), Algorithm world, level 6: is_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Algorithm/L06is_zero.lean, Apache-2.0. -/
theorem primer_algorithm_06_is_zero (a : ℕ) : Nat.succ a ≠ 0 := by
  exact Nat.succ_ne_zero a
