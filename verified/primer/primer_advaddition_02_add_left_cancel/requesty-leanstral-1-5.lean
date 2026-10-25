import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 2: add_left_cancel. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L02add_left_cancel.lean, Apache-2.0. -/
theorem primer_advaddition_02_add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  exact Nat.add_left_cancel
