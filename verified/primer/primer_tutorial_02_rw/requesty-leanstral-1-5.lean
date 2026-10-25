import Mathlib

/-- Natural Number Game (Lean 4), Tutorial world, level 2: the rw tactic. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Tutorial/L02rw.lean, Apache-2.0. -/
theorem primer_tutorial_02_rw (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]
