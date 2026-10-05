import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 4: le_trans. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L04le_trans.lean, Apache-2.0. -/
theorem primer_lessorequal_04_le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  exact le_trans hxy hyz
