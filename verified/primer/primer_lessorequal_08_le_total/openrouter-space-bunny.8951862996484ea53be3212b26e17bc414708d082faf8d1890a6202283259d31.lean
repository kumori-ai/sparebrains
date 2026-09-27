import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 8: le_total. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L08le_total.lean, Apache-2.0. -/
theorem primer_lessorequal_08_le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  omega
