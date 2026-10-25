import Mathlib

/-- Natural Number Game (Lean 4), Algorithm world, level 9: decide again. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Algorithm/L09decide2.lean, Apache-2.0. -/
theorem primer_algorithm_09_decide2 : (2 : ℕ) + 2 ≠ 5 := by
  decide
