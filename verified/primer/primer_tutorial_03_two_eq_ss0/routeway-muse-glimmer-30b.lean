import Mathlib

/-- Natural Number Game (Lean 4), Tutorial world, level 3: Numbers. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Tutorial/L03two_eq_ss0.lean, Apache-2.0. -/
theorem primer_tutorial_03_two_eq_ss0 : (2 : ℕ) = Nat.succ (Nat.succ 0) := by
  rfl
