import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 6: le_antisymm. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L06le_antisymm.lean, Apache-2.0. -/
theorem primer_lessorequal_06_le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  apply le_antisymm
  exact hxy
  exact hyx
