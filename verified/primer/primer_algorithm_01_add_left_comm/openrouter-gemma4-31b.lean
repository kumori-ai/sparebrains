import Mathlib

/-- Natural Number Game (Lean 4), Algorithm world, level 1: add_left_comm. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Algorithm/L01add_left_comm.lean, Apache-2.0. -/
theorem primer_algorithm_01_add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]
