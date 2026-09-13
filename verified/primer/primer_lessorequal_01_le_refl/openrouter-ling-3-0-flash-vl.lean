import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 1: The use tactic. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L01le_refl.lean, Apache-2.0. -/
theorem primer_lessorequal_01_le_refl (x : ℕ) : x ≤ x := by
  rfl
