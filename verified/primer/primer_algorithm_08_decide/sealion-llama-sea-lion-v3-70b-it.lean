import Mathlib

/-- Natural Number Game (Lean 4), Algorithm world, level 8: decide. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Algorithm/L08decide.lean, Apache-2.0. -/
theorem primer_algorithm_08_decide : (20 : ℕ) + 20 = 40 := by
  ring
