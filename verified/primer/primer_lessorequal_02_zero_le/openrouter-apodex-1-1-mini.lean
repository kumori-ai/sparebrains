import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 2: 0 ≤ x. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L02zero_le.lean, Apache-2.0. -/
theorem primer_lessorequal_02_zero_le (x : ℕ) : 0 ≤ x := by
  exact Nat.zero_le x
