import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 3: x ≤ succ x. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L03le_succ_self.lean, Apache-2.0. -/
theorem primer_lessorequal_03_le_succ_self (x : ℕ) : x ≤ Nat.succ x := by
  simp [Nat.le_succ]
