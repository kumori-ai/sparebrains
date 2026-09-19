import Mathlib

/-- Natural Number Game (Lean 4), Addition world, level 1: zero_add. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Addition/L01zero_add.lean, Apache-2.0. -/
theorem primer_addition_01_zero_add (n : ℕ) : 0 + n = n := by
  exact Nat.zero_add n
