import Mathlib

/-- Natural Number Game (Lean 4), Tutorial world, level 1: The rfl tactic. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Tutorial/L01rfl.lean, Apache-2.0. -/
theorem primer_tutorial_01_rfl (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl
