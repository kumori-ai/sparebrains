import Mathlib

/-- Natural Number Game (Lean 4), Addition world, level 2: succ_add. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Addition/L02succ_add.lean, Apache-2.0. -/
theorem primer_addition_02_succ_add (a b : ℕ) : Nat.succ a + b = Nat.succ (a + b) := by
  exact Nat.succ_add a b
