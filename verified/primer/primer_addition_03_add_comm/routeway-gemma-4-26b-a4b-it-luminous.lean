import Mathlib

/-- Natural Number Game (Lean 4), Addition world, level 3: add_comm (level boss). Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Addition/L03add_comm.lean, Apache-2.0. -/
theorem primer_addition_03_add_comm (a b : ℕ) : a + b = b + a := by
  rw [Nat.add_comm]
