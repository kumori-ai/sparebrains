import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 5: x ≤ 0 → x = 0. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L05le_zero.lean, Apache-2.0. -/
theorem primer_lessorequal_05_le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  exact le_antisymm hx (Nat.zero_le x)
