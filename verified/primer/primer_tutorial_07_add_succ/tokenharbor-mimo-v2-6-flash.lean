import Mathlib

/-- Natural Number Game (Lean 4), Tutorial world, level 7: add_succ. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Tutorial/L07add_succ.lean, Apache-2.0. -/
theorem primer_tutorial_07_add_succ (n : ℕ) : Nat.succ n = n + 1 := by
  omega
