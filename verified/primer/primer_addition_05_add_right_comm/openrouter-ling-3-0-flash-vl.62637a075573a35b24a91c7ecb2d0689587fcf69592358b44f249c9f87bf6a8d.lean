import Mathlib

/-- Natural Number Game (Lean 4), Addition world, level 5: add_right_comm. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Addition/L05add_right_comm.lean, Apache-2.0. -/
theorem primer_addition_05_add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  exact Nat.add_right_comm a b c
