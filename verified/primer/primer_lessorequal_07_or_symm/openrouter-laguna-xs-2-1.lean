import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 7: Dealing with or. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L07or_symm.lean, Apache-2.0. -/
theorem primer_lessorequal_07_or_symm (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  exact Or.symm h
